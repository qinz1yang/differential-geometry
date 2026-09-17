import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Metric.DirectLimit.Distance
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}

section Static

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [CompleteSpace E] in
private theorem continuous_riemannianEDistOf (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun y => riemannianEDistOf (I := I) g p y) := by
  exact continuous_riemannianEDist (I := I) g p

omit [CompleteSpace E] in
theorem closedBall_subset_image_of_metric_lower
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv I I (F : N → M) y v)
          (mfderiv I I (F : N → M) y v)) :
    riemannianClosedBallOf (I := I) g (F p) r ⊆
      (F : N → M) '' riemannianClosedBallOf (I := I) h p R := by
  classical
  let B := riemannianClosedBallOf (I := I) h p R
  let U := riemannianBallOf (I := I) h p R
  let K := (F : N → M) '' B
  have hUB : U ⊆ B := by
    intro y hy
    change riemannianEDistOf (I := I) h p y ≤ ENNReal.ofReal R
    exact le_of_lt hy
  have hUopen : IsOpen U := isOpen_lt (continuous_riemannianEDistOf h p) continuous_const
  have hpU : p ∈ U := by
    change riemannianEDistOf (I := I) h p p < ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR
  have hKcpt : IsCompact K :=
    hcpt.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hsource)
  have hFKopen : IsOpen ((F : N → M) '' U) :=
    F.toOpenPartialHomeomorph.isOpen_image_of_subset_source hUopen (hUB.trans hsource)
  have hFKint : (F : N → M) '' U ⊆ interior K :=
    interior_maximal (Set.image_mono hUB) hFKopen
  have hKtarget : K ⊆ F.target := by
    rintro z ⟨y, hy, rfl⟩
    exact F.map_source' (hsource hy)
  intro z hz
  by_contra hzK
  have hzlt : riemannianEDistOf (I := I) g (F p) z < ENNReal.ofReal (R / L) :=
    lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (div_pos hR hL)).mpr hr)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt (I := I) g hzlt
  obtain ⟨t, ht, hstay, hfront⟩ := exists_first_exit_frontier
    hKcpt.isClosed zero_lt_one hγ.continuousOn
    (hγ0 ▸ hFKint ⟨p, hpU, rfl⟩) (by simpa only [hγ1] using hzK)
  have hfront' : γ t ∈ K ∧ γ t ∉ interior K := by
    simpa only [frontier, hKcpt.isClosed.closure_eq, Set.mem_sdiff] using hfront
  let β : ℝ → N := (F.symm : M → N) ∘ γ
  have hβball : ∀ s ∈ Set.Icc (0 : ℝ) t, β s ∈ B := by
    intro s hs
    obtain ⟨y, hy, hFy⟩ := hstay s hs
    change (F.symm : M → N) (γ s) ∈ B
    have hleft : (F.symm : M → N) (F y) = y := F.left_inv' (hsource hy)
    rw [← hFy, hleft]
    exact hy
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 β (Set.Icc 0 t) :=
    (F.symm.contMDiffOn_toFun.of_le (by simp)).comp
      (hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)) (fun s hs => hKtarget (hstay s hs))
  have hβ0 : β 0 = p := by
    change (F.symm : M → N) (γ 0) = p
    rw [hγ0]
    exact F.left_inv' (hsource (hUB hpU))
  have hexit : ENNReal.ofReal R ≤ riemannianEDistOf (I := I) h p (β t) := by
    apply le_of_not_gt
    intro hdist
    apply hfront'.2
    apply hFKint
    exact ⟨β t, hdist, F.right_inv' (hKtarget hfront'.1)⟩
  have hspeed : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Real.sqrt (h.inner (β s) (mfderiv 𝓘(ℝ, ℝ) I β s 1)
        (mfderiv 𝓘(ℝ, ℝ) I β s 1)) ≤
      L * Real.sqrt (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) := by
    intro s hs
    have hscc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
    have hstgt : γ s ∈ F.target := hKtarget (hstay s hscc)
    have hβd : MDifferentiableAt 𝓘(ℝ, ℝ) I β s :=
      (hβ.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt (by norm_num)
    have hFd : MDifferentiableAt I I (F : N → M) (β s) :=
      (F.contMDiffOn_toFun.contMDiffAt
        (F.open_source.mem_nhds (hsource (hβball s hscc)))).mdifferentiableAt (by simp)
    have heq : (F : N → M) ∘ β =ᶠ[nhds s] γ := by
      have hγc : ContinuousAt γ s := hγ.continuousOn.continuousAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
      filter_upwards [hγc.preimage_mem_nhds (F.open_target.mem_nhds hstgt)] with q hq
      exact F.right_inv' hq
    have hderiv : mfderiv I I (F : N → M) (β s) (mfderiv 𝓘(ℝ, ℝ) I β s 1) =
        mfderiv 𝓘(ℝ, ℝ) I γ s 1 := by
      rw [← mfderiv_comp_apply s hFd hβd, heq.mfderiv_eq]
      rfl
    have hcompval : F (β s) = γ s := F.right_inv' hstgt
    have hinnerEq :
        g.inner (F (β s)) (mfderiv I I (F : N → M) (β s)
          (mfderiv 𝓘(ℝ, ℝ) I β s 1))
          (mfderiv I I (F : N → M) (β s) (mfderiv 𝓘(ℝ, ℝ) I β s 1)) =
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) := by
      rw [hderiv, hcompval]
    have hbd := hlower (β s) (hβball s hscc) (mfderiv 𝓘(ℝ, ℝ) I β s 1)
    rw [hinnerEq] at hbd
    calc
      _ ≤ Real.sqrt (L ^ 2 * g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) := Real.sqrt_le_sqrt hbd
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]
  have hlift : metricPathELength (I := I) h β 0 t ≤
      ENNReal.ofReal L * metricPathELength (I := I) g γ 0 t := by
    rw [metricPathELength_eq, metricPathELength_eq, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
    rw [← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (hspeed s hs)
  have hliftlt : metricPathELength (I := I) h β 0 t < ENNReal.ofReal R := by
    calc
      _ ≤ ENNReal.ofReal L * metricPathELength (I := I) g γ 0 t := hlift
      _ ≤ ENNReal.ofReal L * metricPathELength (I := I) g γ 0 1 :=
        mul_le_mul_right (metricPathELength_mono (I := I) g γ le_rfl ht.2) _
      _ < ENNReal.ofReal L * ENNReal.ofReal (R / L) :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_ne_zero_iff.mpr hL)
          ENNReal.ofReal_ne_top hlen
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_mul hL.le, mul_div_cancel₀ R hL.ne']
  have hdist := edistOf_le_metricPathELength (I := I) h ht.1.le hβ
  rw [hβ0] at hdist
  exact (not_lt_of_ge hexit) (hdist.trans_lt hliftlt)

end Static

section Witness

variable [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
  {x : M} {t kappa : ℝ}

omit [SigmaCompactSpace M] in
theorem witnessSourceBallCapture_on_window
    (W : KappaModelWitness.{u, uE, uH} (I := I) (1 / 4) kappa S x t)
    {s : ℝ} (hs : s ∈ Set.Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s) x 1) ∧
      riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s) x 1 ⊆
        witnessImage (I := I) W := by
  let : TopologicalSpace W.model.M := W.model.topology
  let : ChartedSpace H W.model.M := W.model.charted
  let : IsManifold I ∞ W.model.M := W.model.smooth
  let : IsManifold I 1 W.model.M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
  let : T2Space W.model.M := W.model.t2
  let : T2Space (TangentBundle I W.model.M) := W.model.t2TangentBundle
  let B := riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint 2
  have hBcompact : IsCompact B := by
    apply RiemannianMetricComplete.closedEBall_isCompact
    refine ⟨?_⟩
    with_unfolding_all
      exact MetricComplete.complete (I := I) (W.model.atTime (I := I) 0)
        (W.model_ancient.complete 0 (by simp))
  have hBsource : B ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono (I := I) (W.model.S.base.metric 0) W.model.basepoint
      (by rw [modelRadius_quarter]; norm_num : (2 : ℝ) ≤ modelRadius (1 / 4) + 1)).trans
      W.comparison.buffered_ball_subset
  have hcapture : riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s)
      (W.embedding W.model.basepoint) 1 ⊆ (W.embedding : W.model.M → M) '' B := by
    apply closedBall_subset_image_of_metric_lower (W.model.S.base.metric 0)
      (witnessGhat (I := I) W s) W.embedding W.model.basepoint
      (L := (3 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hBcompact hBsource
    intro y hy v
    have htime := ancientModel_metric_zero_le W.model W.model_ancient hs.2 y v
    have hswin : s ∈ Set.Icc (-(modelDepth (1 / 4))) (0 : ℝ) := by
      simpa only [modelDepth, one_div, inv_inv] using hs
    have hywin : y ∈ riemannianClosedBallOf (I := I) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius (1 / 4)) := by
      simpa only [modelRadius_quarter] using hy
    have hlower := (W.comparison.metric_equivalence s hswin y hywin v).1
    rw [W.comparison.pullback_apply s y (W.comparison.buffered_ball_subset
      (riemannianClosedBallOf_mono (I := I) _ _ (by linarith) hywin))]
      at hlower
    have hnonneg := inner_self_nonneg (I := I) (witnessGhat (I := I) W s)
      (W.embedding y) (mfderiv I I (W.embedding : W.model.M → M) y v)
    change (1 - (1 / 4 : ℝ)) * (W.model.S.base.metric s).inner y v v ≤
      (witnessGhat (I := I) W s).inner (W.embedding y)
        (mfderiv I I (W.embedding : W.model.M → M) y v)
        (mfderiv I I (W.embedding : W.model.M → M) y v) at hlower
    nlinarith
  rw [W.comparison.base_map] at hcapture
  have hmodelBall : B = witnessModelBall (I := I) W := by
    change riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint 2 =
      riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint
        (modelRadius (1 / 4))
    rw [modelRadius_quarter]
  have himageCompact : IsCompact ((W.embedding : W.model.M → M) '' B) :=
    hBcompact.image_of_continuousOn
      (W.embedding.contMDiffOn_toFun.continuousOn.mono hBsource)
  constructor
  · exact himageCompact.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDistOf (witnessGhat (I := I) W s) x)
        continuous_const) hcapture
  · simpa only [hmodelBall, witnessImage] using hcapture

theorem witnessSourceBallCapture : WitnessSourceBallCapture.{u, uE, uH} I kappa := by
  intro M _ _ _ _ _ _ D S x t W
  exact witnessSourceBallCapture_on_window W (by norm_num)

end Witness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
