import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingOppositeArms
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped _root_.Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

abbrev spatialRescaledPointedSeq (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj i := {
    M := M
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := x i
    metric := scaleMetric (lam i ^ 2) (sq_pos_of_pos (hlam i)) g }

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem spatialRescaledPointedSeq_edist (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (i : ℕ) (y z : M) :
    riemannianEDistOf (I := I) ((spatialRescaledPointedSeq g x lam hlam).obj i).metric y z =
      ENNReal.ofReal (lam i) * riemannianEDistOf (I := I) g y z := by
  change riemannianEDistOf (I := I)
    (scaleMetric (lam i ^ 2) (sq_pos_of_pos (hlam i)) g) y z = _
  rw [edistOf_scale, Real.sqrt_sq (hlam i).le]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem spatialRescaledPointedSeq_dist (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (i : ℕ) (y z : M) :
    (riemannianEDistOf (I := I)
      ((spatialRescaledPointedSeq g x lam hlam).obj i).metric y z).toReal =
      lam i * (riemannianEDistOf (I := I) g y z).toReal := by
  rw [spatialRescaledPointedSeq_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hlam i).le]

omit [CompleteSpace E] in
theorem spatialRescaledPointedSeq_complete (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) :
    SeqMetricComplete (I := I) (spatialRescaledPointedSeq g x lam hlam) := by
  constructor
  intro i
  have hscaled : RiemannianMetricComplete (I := I)
      (scaleMetric (lam i ^ 2) (sq_pos_of_pos (hlam i)) g) :=
    hg.of_lower (sq_pos_of_pos (hlam i)) (fun y v => by
      simp only [scaleMetric_inner, le_refl])
  exact hscaled.complete

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem spatialRescaledPointedSeq_connected [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (i : ℕ) :
    @ConnectedSpace ((spatialRescaledPointedSeq g x lam hlam).obj i).M
      ((spatialRescaledPointedSeq g x lam hlam).obj i).topology :=
  inferInstance

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem spatialRescaledPointedSeq_subseq (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (phi : ℕ → ℕ) :
    (spatialRescaledPointedSeq g x lam hlam).subseq phi =
      spatialRescaledPointedSeq g (x ∘ phi) (lam ∘ phi) (fun i => hlam (phi i)) := rfl

section PointedMaps

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem spatialRescaledPointedSeq_basepoint_map (g : SmoothRiemannianMetric I M)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      (spatialRescaledPointedSeq g x lam hlam) L subseq) (k : ℕ) :
    Phi.map k L.basepoint = x (subseq k) := Phi.basepoint_map k

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem reference_eq_limit_compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (k : ℕ) :
    ((C.compSubseq phi hphi).domain k).referenceMetric =
      ((C.compSubseq phi hphi).domain k).limitMetric := hreference (phi k)

end PointedMaps

section IntrinsicArms

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
private theorem rescaledArms_real_triangle (y z w : M) :
    (riemannianEDist I y w).toReal ≤
      (riemannianEDist I y z).toReal + (riemannianEDist I z w).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) y z,
      riemannianEDist_ne_top (I := I) z w⟩)
    (riemannianEDist_triangle (I := I) (x := y) (y := z) (z := w))
  simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) y z)
    (riemannianEDist_ne_top (I := I) z w)] using h

omit [CompleteSpace E] in
private theorem rescaledArms_subsegment_dist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (hv : g.inner p v v = 1)
    (a : ℝ) (ha : 0 < a)
    (hmin : (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p v a)).toReal = a)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hsa : s ≤ a) (hta : t ≤ a) :
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm p v s)
      (intrinsicGeodesic (I := I) g hEnorm p v t)).toReal = |s - t| := by
  have hradial (r : ℝ) (hr : 0 ≤ r) (hra : r ≤ a) :=
    unit_intrinsic_subsegment_dist (I := I) g hEnorm p v hv a r ha hr hra hmin
  have hordered (r q : ℝ) (hr : 0 ≤ r) (hrq : r ≤ q) (hqa : q ≤ a) :
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm p v r)
        (intrinsicGeodesic (I := I) g hEnorm p v q)).toReal = q - r := by
    have hupper := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hrq
    rw [hv, Real.sqrt_one, one_mul] at hupper
    have hupperReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hrq)] at hupperReal
    have htri := rescaledArms_real_triangle (I := I) p
      (intrinsicGeodesic (I := I) g hEnorm p v r)
      (intrinsicGeodesic (I := I) g hEnorm p v q)
    rw [hradial r hr (hrq.trans hqa), hradial q (hr.trans hrq) hqa] at htri
    linarith
  rcases le_total s t with hst | hts
  · rw [hordered s t hs hst hta, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  · rw [riemannianEDist_comm, hordered t s ht hts hsa,
      abs_of_nonneg (sub_nonneg.mpr hts)]

omit [CompleteSpace E] [ConnectedSpace M] in
theorem spatialRescaledPointedSeq_intrinsic_edist_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (i : ℕ) (v : TangentSpace I (x i)) (hv : g.inner (x i) v v = 1)
    (r : ℝ) (hr : 0 ≤ r) :
    riemannianEDistOf (I := I) ((spatialRescaledPointedSeq g x lam hlam).obj i).metric
      (x i) (intrinsicGeodesic (I := I) g hEnorm (x i) v (r / lam i)) ≤
        ENNReal.ofReal r := by
  rw [spatialRescaledPointedSeq_edist,
    riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
  have hupper := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm (x i) v
    (s := 0) (t := r / lam i) (div_nonneg hr (hlam i).le)
  rw [intrinsicGeodesic_zero, hv, Real.sqrt_one, one_mul, sub_zero] at hupper
  calc
    _ ≤ ENNReal.ofReal (lam i) * ENNReal.ofReal (r / lam i) :=
      mul_le_mul_right hupper _
    _ = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (hlam i).le, mul_div_cancel₀ r (hlam i).ne']

omit [CompleteSpace E] in
theorem eventually_spatialRescaledPointedSeq_intrinsic_dist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (v : ∀ i, TangentSpace I (x i)) (hv : ∀ i, g.inner (x i) (v i) (v i) = 1)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hmin : ∀ i, (riemannianEDist I (x i)
      (intrinsicGeodesic (I := I) g hEnorm (x i) (v i) (a i))).toReal = a i)
    (hfar : Tendsto (fun i => lam i * a i) atTop atTop)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᶠ i in atTop, (riemannianEDistOf (I := I)
      ((spatialRescaledPointedSeq g x lam hlam).obj i).metric
      (intrinsicGeodesic (I := I) g hEnorm (x i) (v i) (s / lam i))
      (intrinsicGeodesic (I := I) g hEnorm (x i) (v i) (t / lam i))).toReal = |s - t| := by
  filter_upwards [hfar (eventually_ge_atTop (max s t))] with i hi
  have hsa : s / lam i ≤ a i := (div_le_iff₀ (hlam i)).2 (by
    calc s ≤ max s t := le_max_left s t
      _ ≤ lam i * a i := hi
      _ = a i * lam i := mul_comm _ _)
  have hta : t / lam i ≤ a i := (div_le_iff₀ (hlam i)).2 (by
    calc t ≤ max s t := le_max_right s t
      _ ≤ lam i * a i := hi
      _ = a i * lam i := mul_comm _ _)
  rw [spatialRescaledPointedSeq_dist,
    riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm,
    rescaledArms_subsegment_dist (I := I) g hEnorm (x i) (v i) (hv i)
      (a i) (ha i) (hmin i) (s / lam i) (t / lam i)
      (div_nonneg hs (hlam i).le) (div_nonneg ht (hlam i).le) hsa hta,
    ← sub_div, abs_div, abs_of_pos (hlam i), mul_div_cancel₀ _ (hlam i).ne']

theorem exists_spatialRescaledPointedSeq_approximate_opposite_rays
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDist I p (x i)).toReal) atTop atTop)
    (hscaled : Tendsto (fun i => lam i * (riemannianEDist I p (x i)).toReal)
      atTop atTop) :
    let X := spatialRescaledPointedSeq g x lam hlam
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ alpha beta : ℕ → ℝ → M,
      (∀ n, alpha n 0 = x (phi n) ∧ beta n 0 = x (phi n)) ∧
      (∀ n r, 0 ≤ r →
        riemannianEDistOf (I := I) (X.obj (phi n)).metric (x (phi n)) (alpha n r) ≤
          ENNReal.ofReal r ∧
        riemannianEDistOf (I := I) (X.obj (phi n)).metric (x (phi n)) (beta n r) ≤
          ENNReal.ofReal r) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → ∀ᶠ n in atTop,
        (riemannianEDistOf (I := I) (X.obj (phi n)).metric
          (alpha n s) (alpha n t)).toReal = |s - t| ∧
        (riemannianEDistOf (I := I) (X.obj (phi n)).metric
          (beta n s) (beta n t)).toReal = |s - t|) ∧
      (∀ r, 0 ≤ r → Tendsto (fun n =>
        (riemannianEDistOf (I := I) (X.obj (phi n)).metric
          (alpha n r) (beta n r)).toReal) atTop (𝓝 (2 * r))) := by
  dsimp only
  obtain ⟨phi, hphi, wMinus, wPlus, hunit, hminus, hplus, hpositive,
    hfarMinus, hfarPlus, hopposite⟩ :=
    exists_escaping_opposite_intrinsic_arms (I := I) g hEnorm hsec p x lam hlam
      hescape hscaled
  let q : ℕ → M := x ∘ phi
  let scale : ℕ → ℝ := lam ∘ phi
  have hscale (n : ℕ) : 0 < scale n := hlam (phi n)
  let a : ℕ → ℝ := fun n => (riemannianEDist I p (q n)).toReal
  let b : ℕ → ℝ := fun n => (riemannianEDist I (q n) (q (n + 1))).toReal
  let alpha : ℕ → ℝ → M := fun n r =>
    intrinsicGeodesic (I := I) g hEnorm (q n) (wMinus n) (r / scale n)
  let beta : ℕ → ℝ → M := fun n r =>
    intrinsicGeodesic (I := I) g hEnorm (q n) (wPlus n) (r / scale n)
  have ha (n : ℕ) : 0 < a n := by
    have h := (hpositive n).1
    change 1 ≤ a n at h
    linarith
  have hb (n : ℕ) : 0 < b n := (ha n).trans_le (hpositive n).2
  have hminMinus (n : ℕ) : (riemannianEDist I (q n)
      (intrinsicGeodesic (I := I) g hEnorm (q n) (wMinus n) (a n))).toReal = a n := by
    dsimp only [a, q, Function.comp_def]
    rw [hminus n, riemannianEDist_comm]
  have hminPlus (n : ℕ) : (riemannianEDist I (q n)
      (intrinsicGeodesic (I := I) g hEnorm (q n) (wPlus n) (b n))).toReal = b n := by
    dsimp only [b, q, Function.comp_def]
    rw [hplus n]
  have hcenter (n : ℕ) : alpha n 0 = x (phi n) ∧ beta n 0 = x (phi n) := by
    constructor
    · dsimp only [alpha, q, Function.comp_def]
      rw [zero_div, intrinsicGeodesic_zero]
    · dsimp only [beta, q, Function.comp_def]
      rw [zero_div, intrinsicGeodesic_zero]
  refine ⟨phi, hphi, alpha, beta, hcenter, ?_, ?_, ?_⟩
  · intro n r hr
    exact ⟨spatialRescaledPointedSeq_intrinsic_edist_le (I := I) g hEnorm q scale hscale
      n (wMinus n) (hunit n).1 r hr,
      spatialRescaledPointedSeq_intrinsic_edist_le (I := I) g hEnorm q scale hscale
        n (wPlus n) (hunit n).2 r hr⟩
  · intro s t hs ht
    have hleft := eventually_spatialRescaledPointedSeq_intrinsic_dist (I := I)
      g hEnorm q scale hscale wMinus (fun n => (hunit n).1) a ha hminMinus
      hfarMinus s t hs ht
    have hright := eventually_spatialRescaledPointedSeq_intrinsic_dist (I := I)
      g hEnorm q scale hscale wPlus (fun n => (hunit n).2) b hb hminPlus
      hfarPlus s t hs ht
    exact hleft.and hright
  · intro r hr
    rcases eq_or_lt_of_le hr with hrzero | hrpos
    · subst r
      simpa only [alpha, beta, zero_div, intrinsicGeodesic_zero, riemannianEDistOf_self,
        ENNReal.toReal_zero, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · refine (hopposite r hrpos).congr' (Eventually.of_forall fun n => ?_)
      have hpoint := spatialRescaledPointedSeq_dist (I := I) g x lam hlam
        (phi n) (alpha n r) (beta n r)
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] at hpoint
      exact hpoint.symm

end IntrinsicArms

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
