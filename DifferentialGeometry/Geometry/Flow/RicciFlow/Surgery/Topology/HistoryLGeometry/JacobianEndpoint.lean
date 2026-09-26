import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianSeam

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

open private mem_regularizedStage_Icc mem_regularizedStage_Ioo eq_of_mem_Ioo_of_mem_Icc
  IsHistoryLGeodesicPrefix HasPrefixFamily hasPrefixFamily_end from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private LWindowChain.exists_contMDiff_eqOn from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w : ℝ} {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_end_family (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) :
    ∃ (lo hi : Fin (H.eventCount + 1)) (_ : first ≤ lo) (_ : hi ≤ last)
      (Wv : H.LWindow lo hi T) (hk : lo ≤ first ∧ first ≤ hi) (η : ℝ) (V : Set ThreeSpace)
      (β : ThreeSpace × ℝ → Wv.X), 0 < η ∧ IsOpen V ∧ Z₀.1 ∈ V ∧
      Ioo (w - η) (w + η) ⊆ Ioo Wv.a Wv.b ∧
      (∀ r ∈ Ioo (w - η) (w + η), T - r ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) ∧
      ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ Ioo (w - η) (w + η)) ∧
      (∀ Z ∈ V, IsLRegularizedGeodesicOn Wv.S T (fun s => β (Z, s)) (Ioo (w - η) (w + η))) ∧
      ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p),
        ∀ Z (hZ : Z ∈ V), ∀ r ∈ Ioc (w - η) w,
          H.historyLCurve hle T w p ⟨Z, hVdom Z hZ⟩ ⟨first, le_rfl, hle⟩ r =
            Wv.f ⟨first, hk⟩ (β (Z, r)) := by
  obtain ⟨α₀, hα₀, hinit, W, hvW, γ, hγ, hγα⟩ := hZo
  obtain ⟨V, hV, hZ₀V, A, hA, lo, hi, hlo, hhi, Wv, γv, -, -, -, k, hk, η, hη, hηW, hηk, β, hβ,
    hgeo, -, hAβ⟩ := hasPrefixFamily_end hw hα₀ hinit W hvW γ hγ hγα
  have hvk := hηk w ⟨by linarith, by linarith⟩
  have hfk : first = k := eq_of_mem_Ioo_of_mem_Icc hvk
    ⟨H.time_le_of_mem_stageDomain hα₀.1, H.le_stageEndTime_of_mem_stageDomain hα₀.1⟩
  subst hfk
  have hβv : ∀ Z ∈ V, ContinuousAt (fun r => β (Z, r)) w := fun Z hZ =>
    (((hβ (Z, w) ⟨hZ, by constructor <;> linarith⟩).contMDiffAt
      ((hV.prod isOpen_Ioo).mem_nhds ⟨hZ, by constructor <;> linarith⟩)).comp w
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  have hmem : ∀ Z ∈ V, H.IsHistoryLGeodesicOn hle T w (A Z) ∧
      H.HasHistoryLInitialVector T (A Z) p Z := by
    intro Z hZ
    obtain ⟨hcross, hwin, lo₀, hlo₀, W₀, x, Zx, ha₀, -, hx, hZx, hdom, hbase⟩ := hA Z hZ
    refine ⟨⟨hα₀.1, fun i hf hl => hcross i hf hl ?_, hwin, ?_⟩,
      ⟨lo₀, hlo₀, W₀, x, Zx, ha₀, hx, hZx, hdom, hbase⟩⟩
    · have h1 : H.stageEndTime first ≤ H.time i.succ := by
        rw [← stageEndTime_castSucc]
        exact H.stageEndTime_mono hf
      exact (Real.sqrt_lt' hw).2 (by linarith [hvk.2])
    · have hg : ContinuousAt (fun r => Wv.f ⟨first, hk⟩ (β (Z, r))) w :=
        (Wv.localDiffeomorph _).contMDiff.continuous.continuousAt.comp (hβv Z hZ)
      refine hg.continuousWithinAt.congr_of_eventuallyEq ?_ (hAβ Z hZ w ⟨by linarith, le_rfl⟩)
      filter_upwards [Ioo_mem_nhdsLT (show w - η < w by linarith)] with r hr
      exact hAβ Z hZ r ⟨hr.1, hr.2.le⟩
  have hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p :=
    fun Z hZ => ⟨A Z, hmem Z hZ⟩
  refine ⟨lo, hi, hlo, hhi, Wv, hk, η, V, β, hη, hV, hZ₀V, hηW, hηk, hβ, hgeo, hVdom,
    fun Z hZ r hr => ?_⟩
  have hrk := hηk r ⟨hr.1, by linarith [hr.2]⟩
  have hr0 : 0 ≤ r := by
    have := hηW ⟨hr.1, by linarith [hr.2]⟩
    exact Wv.nonneg.trans this.1.le
  rw [eqOn_historyLCurve hw ⟨Z, hVdom Z hZ⟩ (hmem Z hZ).1 (hmem Z hZ).2 ⟨first, le_rfl, hle⟩
    (mem_regularizedStage_Icc le_rfl ⟨hr0, hr.2⟩ ⟨hrk.1.le, hrk.2.le⟩)]
  exact hAβ Z hZ r hr

theorem paramDensity_eq_lJacobianDensity_sq {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (T : ℝ)
    (β : ThreeSpace × ℝ → X) (z : ThreeSpace) {s : ℝ} (hs : 0 ≤ s) :
    DifferentialGeometry.Integral.Measure.paramDensity (S.base.metric (T - s ^ 2))
        (fun Z => β (Z, s)) z =
      lJacobianDensity S T (fun q => β (z, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) z
          (chartModelBasis ThreeSpace i)) (s ^ 2) := by
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs
  have hpt : β (z, Real.sqrt (s ^ 2)) = β (z, s) := by rw [hsq]
  have hFd : ∀ i, (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt (s ^ 2))) z
      (chartModelBasis ThreeSpace i) : ThreeSpace) =
      mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, s)) z (chartModelBasis ThreeSpace i) := by
    intro i
    rw [hsq]
  unfold lJacobianDensity DifferentialGeometry.Integral.Measure.paramDensity
  congr 2
  ext i j
  exact (inner_congr_point' _ hpt _ _ _ _ (hFd i) (hFd j)).symm

theorem continuousWithinAt_historyReducedJacobianAlong {B₀ : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    (hwk : T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) :
    ContinuousWithinAt (H.historyReducedJacobianAlong Z₀) (Iic w) w := by
  classical
  have hZo := historyMinDomain_subset_historyLExpOpenDomain hw hwk hfloor hZmin
  obtain ⟨lo, hi, hlo, hhi, Wv, hk, η, V, β, hη, hV, hZ₀V, hηW, hηk, hβ, hgeo, hVdom, hrep⟩ :=
    exists_end_family hw Z₀ hZo
  have hstage : ∀ r ∈ Ioo (w - η) (w + η), ∀ j : Fin (H.eventCount + 1),
      T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j) → j = first := fun r hr j hj =>
    eq_of_mem_Ioo_of_mem_Icc (hηk r hr) hj
  set K₁ := Ioo (w - η) w with hK₁
  have hK₁W : K₁ ⊆ Ioo Wv.a Wv.b := fun r hr => hηW ⟨hr.1, by linarith [hr.2]⟩
  have hβ₁ := hβ.mono (prod_mono subset_rfl (show K₁ ⊆ Ioo (w - η) (w + η) from
    fun r hr => ⟨hr.1, by linarith [hr.2]⟩))
  have hrep₁ : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
      ∀ r ∈ K₁ ∩ Ioo (H.regularizedStageStart T Wv.a j.val) (H.regularizedStageEnd T Wv.b j.val),
        H.historyLCurve hle T w p ⟨Z, hVdom Z hZ⟩
          ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = Wv.f j (β (Z, r)) := by
    intro Z hZ j r hr
    obtain ⟨jv, hj1, hj2⟩ := j
    have ht := H.mapsTo_regularizedStage_Ioo T Wv.a Wv.b jv hr.2
    obtain rfl : jv = first := hstage r ⟨hr.1.1, by linarith [hr.1.2]⟩ jv
      ⟨H.time_le_of_mem_stageDomain ht, H.le_stageEndTime_of_mem_stageDomain ht⟩
    exact hrep Z hZ r ⟨hr.1.1, hr.1.2.le⟩
  have hwI : w ∈ Ioo (w - η) (w + η) := ⟨by linarith, by linarith⟩
  have hpiece : ∀ r ∈ Ioo (w - η) (w + η),
      r ∈ Ioo (H.regularizedStageStart T Wv.a first) (H.regularizedStageEnd T Wv.b first) :=
    fun r hr => mem_regularizedStage_Ioo Wv.nonneg (hηW hr) (hηk r hr)
  have hLc := continuousAt_lJacobianDensity_sq (Z₀ := Z₀) hV hZ₀V isOpen_Ioo hηW hβ hgeo hwI
  have hHd1 : ∀ r ∈ K₁, H.historyLJacobianDensity hle T w p Z₀ ⟨first, le_rfl, hle⟩ r =
      lJacobianDensity Wv.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) (r ^ 2) := fun r hr =>
    historyLJacobianDensity_eq_lJacobianDensity_sq (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V
      hVdom isOpen_Ioo hK₁W hβ₁ hrep₁ ⟨first, hk⟩ ⟨hr, hpiece r ⟨hr.1, by linarith [hr.2]⟩⟩
  have hHdw : H.historyLJacobianDensity hle T w p Z₀ ⟨first, le_rfl, hle⟩ w =
      lJacobianDensity Wv.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) (w ^ 2) := by
    have hf : (Wv.f ⟨first, hk⟩ ∘ fun Z => β (Z, w)) =ᶠ[𝓝 Z₀.1]
        H.historyLCurveMap hle T w p Z₀ ⟨first, le_rfl, hle⟩ w := by
      filter_upwards [hV.mem_nhds hZ₀V] with Z hZ
      rw [Function.comp_apply, historyLCurveMap_of_mem _ _ (hVdom Z hZ)]
      exact (hrep Z hZ w ⟨by linarith, le_rfl⟩).symm
    have h1 := paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := Z₀)
      ⟨first, le_rfl, hle⟩ w hf
    have hΨ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, w))
        (show ThreeSpace from Z₀.1) :=
      (((hβ ((show ThreeSpace from Z₀.1), w) ⟨hZ₀V, hwI⟩).contMDiffAt
        ((hV.prod isOpen_Ioo).mem_nhds ⟨hZ₀V, hwI⟩)).comp (show ThreeSpace from Z₀.1)
        (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
    have h2 := DifferentialGeometry.Integral.Measure.paramDensity_comp_of_inner_eq
      (Wv.S.base.metric (T - w ^ 2)) (H.stageMetric first (T - w ^ 2))
      (f := Wv.f ⟨first, hk⟩) (Ψ := fun Z => β (Z, w)) (w := Z₀.1)
      (((Wv.localDiffeomorph _) _).mdifferentiableAt (by simp)) hΨ (fun a b => by
        rw [Wv.metric ⟨first, hk⟩ w (hpiece w hwI), localPullMetric_inner])
    exact h1.symm.trans (h2.trans (paramDensity_eq_lJacobianDensity_sq Wv.S T β Z₀.1 hw.le))
  have hHdc : ContinuousWithinAt (fun r => H.historyLJacobianDensity hle T w p Z₀
      ⟨first, le_rfl, hle⟩ r) (Iic w) w := by
    refine hLc.continuousWithinAt.congr_of_eventuallyEq ?_ hHdw
    filter_upwards [Ioc_mem_nhdsLE (show w - η < w by linarith)] with r hr
    rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h]; exact hHdw
    · exact hHd1 r ⟨hr.1, h⟩
  set v₀ := w - η / 2 with hv₀def
  have hv₀I : v₀ ∈ Ioo (w - η) (w + η) := ⟨by linarith, by linarith⟩
  have hv₀ : 0 < v₀ := Wv.nonneg.trans_lt (hηW hv₀I).1
  have hv₀w : v₀ ≤ w := by linarith
  have hβZ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => β (Z₀.1, s)) (Ioo (w - η) (w + η)) :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hZ₀V, hs⟩
  obtain ⟨γ, hγ, hγeq⟩ := LWindowChain.exists_contMDiff_eqOn (a := v₀) (b := w) (by linarith)
    (show 0 < η / 4 by positivity) (hβZ.mono (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩))
  have hmem₀ := mem_historyLExpDomain_historyStage Z₀ hv₀ hv₀w
  have hκ₀ := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv₀ hv₀w)
  have hsplit : ∀ v' ∈ Ioc v₀ w, H.historyReducedJacobianAlong Z₀ v' =
      H.historyLJacobianDensity hle T w p Z₀ ⟨first, le_rfl, hle⟩ v' / H.historyLSourceDensity T p *
        Real.exp (-(H.historyLAction (historyStage_le_last Z₀ hv₀ hv₀w) T v₀ p ⟨Z₀.1, hmem₀⟩ +
          lRegularizedAction Wv.S T γ v₀ v') / (2 * v') - (3 / 2 : ℝ) * Real.log (v' ^ 2) -
          (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
    intro v' hv'
    have hv'I : v' ∈ Ioo (w - η) (w + η) := ⟨by linarith [hv'.1], by linarith [hv'.2]⟩
    refine historyReducedJacobianAlong_eq_split hfloor hw Z₀ hZmin hZo hlo hhi Wv γ hγ hv₀ hv'.1
      (hηW hv₀I) (hηW hv'I) hv'.2 (fun j r hr ht => ?_) (historyStage_le_last Z₀ hv₀ hv₀w) le_rfl
      hle hκ₀ (H.mem_stageDomain_of_mem_Ioo (hηk v' hv'I)) ⟨Z₀.1, hmem₀⟩ rfl
    obtain ⟨jv, hj1, hj2⟩ := j
    obtain rfl : jv = first := hstage r ⟨by linarith [hr.1], by linarith [hr.2, hv'.2]⟩ jv ht
    rw [hγeq ⟨by linarith [hr.1], by linarith [hr.2, hv'.2]⟩]
    exact hrep Z₀.1 hZ₀V r ⟨by linarith [hr.1], hr.2.trans hv'.2⟩
  have hU : IsOpen {s : ℝ | T - s ^ 2 ∈ Wv.D.regular} := Wv.D.regular_isOpen.preimage (by fun_prop)
  have hLcont : ContinuousOn (lRegularizedLagrangian Wv.S T γ)
      {s : ℝ | T - s ^ 2 ∈ Wv.D.regular} := by
    have hc := lRegularizedLagrangian_continuousOn_carrier Wv.S Wv.solution γ (hγ.of_le (by decide))
    have hh := hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s (hs : s ∈ {s : ℝ | T - s ^ 2 ∈ Wv.D.regular}) =>
        (Wv.D.regular_subset hs : (T, s).1 - (T, s).2 ^ 2 ∈ Wv.D.carrier))
    exact hh
  have hreg : ∀ r ∈ Ioo (w - η) (w + η), r ∈ {s : ℝ | T - s ^ 2 ∈ Wv.D.regular} := fun r hr =>
    Wv.regular r ⟨(hηW hr).1.le, (hηW hr).2.le⟩
  have hIc : ContinuousAt (fun v' => lRegularizedAction Wv.S T γ v₀ v') w :=
    (intervalIntegral.integral_hasDerivAt_right
      ((hLcont.mono fun r hr =>
        hreg r ⟨by linarith [hr.1], by linarith [hr.2]⟩).intervalIntegrable_of_Icc
        (by linarith))
      (hLcont.stronglyMeasurableAtFilter hU w (hreg w hwI))
      (hLcont.continuousAt (hU.mem_nhds (hreg w hwI)))).continuousAt
  have hgc : ContinuousAt (fun v' => Real.exp (-(H.historyLAction (historyStage_le_last Z₀ hv₀ hv₀w)
      T v₀ p ⟨Z₀.1, hmem₀⟩ + lRegularizedAction Wv.S T γ v₀ v') / (2 * v') -
      (3 / 2 : ℝ) * Real.log (v' ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))) w := by
    refine Real.continuous_exp.continuousAt.comp ?_
    refine ((((continuousAt_const.add hIc).neg).div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero two_ne_zero hw.ne')).sub (continuousAt_const.mul ?_)).sub continuousAt_const
    exact ((continuous_pow 2).continuousAt).log (pow_ne_zero 2 hw.ne')
  refine ((hHdc.div_const (H.historyLSourceDensity T p)).mul
    hgc.continuousWithinAt).congr_of_eventuallyEq
    ?_ (hsplit w ⟨by linarith, le_rfl⟩)
  filter_upwards [Ioc_mem_nhdsLE (show v₀ < w by linarith)] with v' hv'
  exact hsplit v' hv'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
