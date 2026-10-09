import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTightness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAsymptoticReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceReducedLength
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Volume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Scaling

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩
private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    MeasurableSpace P.M := borel P.M
private local instance (P : PointedRiemannianManifold.{u, uE, uH} I) :
    BorelSpace P.M := ⟨rfl⟩

theorem normalizedShrinkerMass_eq_asymptoticReducedVolume_of_reducedLength_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) {phi : ℕ → ℕ}
    (hescape : Tendsto (tau ∘ phi) atTop atTop)
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (hcomplete : MetricComplete P) (ell : P.M → ℝ)
    (hlim : ∀ x, Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (phi i)))
      atTop (𝓝 (ell x))) :
    normalizedShrinkerMass P.metric ell = asymptoticReducedVolume F.S 0 p := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : ConnectedSpace F.M := hF.connected
  let X := backwardSliceSequence F tau htau q
  let c : ℝ := (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)
  have hc : 0 ≤ c := mul_nonneg (by positivity)
    (Real.log_nonneg (by linarith [Real.pi_gt_three]))
  let fs : ∀ i, (X.obj i).M → ℝ≥0∞ :=
    fun i x => ENNReal.ofReal (Real.exp (-redLength F.S 0 p x (tau i) - c))
  let f : P.M → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-ell x - c))
  let μ : ℕ → Measure F.M := fun i =>
    riemannianVolumeMeasure (I := I) (M := F.M) (X.obj i).metric
  let ν := riemannianVolumeMeasure (I := I) (M := P.M) P.metric
  have hnonneg (i : ℕ) (x : F.M) : 0 ≤ redLength F.S 0 p x (tau i) := by
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 (htau i).le
    intro t ht y
    simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1
  have hmeas (i : ℕ) : Measurable (fs i) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        ((continuous_redLength_of_ancient F hF p (htau i)).neg.sub continuous_const)).measurable
  have hbound (i : ℕ) (x : F.M) : fs i x ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (by linarith [hnonneg i x])
  have htotal : Tendsto (fun i => ∫⁻ x, fs (phi i) x ∂μ (phi i)) atTop
      (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
    have ht := (ancient_reducedVolume_tendsto_atTop F hF p).comp hescape
    apply ht.congr'
    apply Eventually.of_forall
    intro i
    dsimp only [Function.comp_apply]
    rw [intrinsicReducedVolume_eq_normalizedShrinkerMass F.S 0 p (htau (phi i))]
    simp only [zero_sub]
    rfl
  change (∫⁻ x, f x ∂ν) = asymptoticReducedVolume F.S 0 p
  apply Phi.lintegral_eq_of_tendsto_of_tightness C hcanonical hcomplete fs hmeas
    (fun K _ => ⟨1, ENNReal.one_ne_top,
      Eventually.of_forall (fun i x _ => hbound (phi i) (Phi.map i x))⟩)
    (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp ((hlim x).neg.sub_const c))) htotal
  intro ε hε
  obtain ⟨N, hN⟩ := ancient_exp_neg_redLength_uniform_tightness F hF
    (ell P.basepoint + 1) hε
  refine ⟨N, ?_⟩
  have hbase : ∀ᶠ i in atTop,
      redLength F.S 0 p (q (phi i)) (tau (phi i)) ≤ ell P.basepoint + 1 := by
    filter_upwards [(hlim P.basepoint).eventually
      (gt_mem_nhds (lt_add_one (ell P.basepoint)))] with i hi
    simpa only [PointedRiemannianConvergenceMaps.map, Phi.basepoint_map] using hi.le
  filter_upwards [hbase] with i hi
  let T := {x : F.M | (N : ℝ) ≤ (riemannianEDistOf (X.obj (phi i)).metric (q (phi i)) x).toReal}
  have hsubset : (riemannianBallOf (X.obj (phi i)).metric (q (phi i)) (N : ℝ))ᶜ ⊆ T := by
    intro x hx
    have hn : ENNReal.ofReal (N : ℝ) ≤
        riemannianEDistOf (X.obj (phi i)).metric (q (phi i)) x := le_of_not_gt hx
    have hd := ENNReal.toReal_mono
      (riemannianEDistOf_ne_top (X.obj (phi i)).metric (q (phi i)) x) hn
    change (N : ℝ) ≤ (riemannianEDistOf (X.obj (phi i)).metric (q (phi i)) x).toReal
    simpa only [ENNReal.toReal_ofReal (Nat.cast_nonneg N)] using hd
  calc
    _ ≤ ∫⁻ x in T, fs (phi i) x ∂μ (phi i) := lintegral_mono_set hsubset
    _ ≤ ∫⁻ x in T, ENNReal.ofReal (Real.exp (-redLength F.S 0 p x (tau (phi i))))
        ∂μ (phi i) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ ε := hN p (q (phi i)) (tau (phi i)) (htau (phi i)) hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

theorem exists_backward_slice_reducedLength_limit_with_mass
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : Tendsto tau atTop atTop) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
        (C : MetricConvergenceData Phi),
        (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) ∧
        (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∃ ell : C(P.M, ℝ), (∀ x, 0 ≤ ell x) ∧ ell P.basepoint ≤ A ∧
          (∀ x y, |Real.sqrt (ell x) - Real.sqrt (ell y)| ≤
            Real.sqrt 3 / 2 * (riemannianEDistOf P.metric x y).toReal) ∧
          (∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
            (fun i x => redLength F.S 0 p (Phi.map i x) (tau (phi i))) ell atTop K) ∧
          normalizedShrinkerMass P.metric ell = asymptoticReducedVolume F.S 0 p := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  obtain ⟨P, phi, hphi, Phi, C, hcanonical, href, hcomplete, hconnected,
      ell, hnonneg, hbaseLimit, hLip, hconv⟩ :=
    exists_backward_slice_reducedLength_limit F hF p tau htau q hbase
  refine ⟨P, phi, hphi, Phi, C, hcanonical, href, hcomplete, hconnected,
    ell, hnonneg, hbaseLimit, hLip, hconv, ?_⟩
  exact normalizedShrinkerMass_eq_asymptoticReducedVolume_of_reducedLength_limit F hF
    p tau htau q P (hescape.comp hphi.tendsto_atTop) Phi C hcanonical hcomplete ell
    (fun x => (hconv {x} isCompact_singleton).tendsto_at (mem_singleton x))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
