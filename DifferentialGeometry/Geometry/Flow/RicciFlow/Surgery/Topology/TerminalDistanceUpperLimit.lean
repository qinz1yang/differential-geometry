import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem path_integral_subtype_le
    {P : OrientedThreeStage.{u}} (U : TopologicalSpace.Opens P.Carrier)
    (g : P.Metric) (gbar : SmoothRiemannianMetric ThreeModel U)
    {x y : U} (γ : Path x y) (hγ : ContMDiff (𝓡∂ 1) ThreeModel 1 γ)
    {c : ℝ} (hc : 0 ≤ c)
    (hquad : ∀ z ∈ Set.range γ, ∀ v : TangentSpace ThreeModel z,
      (g.restrictOpen U).inner z v v ≤ c ^ 2 * gbar.inner z v v) :
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      (g.inner ((γ.map continuous_subtype_val) t)
        (mfderiv (𝓡∂ 1) ThreeModel (γ.map continuous_subtype_val) t 1)
        (mfderiv (𝓡∂ 1) ThreeModel (γ.map continuous_subtype_val) t 1)))) ≤
      ENNReal.ofReal c * ∫⁻ t, ENNReal.ofReal (Real.sqrt
        (gbar.inner (γ t) (mfderiv (𝓡∂ 1) ThreeModel γ t 1) (mfderiv (𝓡∂ 1) ThreeModel γ t 1))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hder := mfderiv_comp t
    (hasMFDerivAt_subtype_val (I := ThreeModel) U (γ t)).mdifferentiableAt
    (hγ.mdifferentiableAt one_ne_zero)
  change mfderiv (𝓡∂ 1) ThreeModel (γ.map continuous_subtype_val) t = _ at hder
  rw [hder, mfderiv_subtype_val]
  change Real.sqrt ((g.restrictOpen U).inner (γ t)
      (mfderiv (𝓡∂ 1) ThreeModel γ t 1) (mfderiv (𝓡∂ 1) ThreeModel γ t 1)) ≤
    c * Real.sqrt (gbar.inner (γ t) (mfderiv (𝓡∂ 1) ThreeModel γ t 1) (mfderiv (𝓡∂ 1) ThreeModel γ t 1))
  calc
    _ ≤ Real.sqrt (c ^ 2 * gbar.inner (γ t)
        (mfderiv (𝓡∂ 1) ThreeModel γ t 1) (mfderiv (𝓡∂ 1) ThreeModel γ t 1)) :=
      Real.sqrt_le_sqrt (hquad (γ t) ⟨t, rfl⟩ _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (x y : G.terminalRegularOpen)
    (hfin : riemannianEDistOf L.metric x y ≠ ⊤)
    (η : ℝ) (hη : 0 < η) :
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
      riemannianEDistOf (G.flow.base.metric t) x.val y.val ≤
        riemannianEDistOf L.metric x y + ENNReal.ofReal η := by
  let D : ℝ := (riemannianEDistOf L.metric x y).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  have hDeq : ENNReal.ofReal D = riemannianEDistOf L.metric x y :=
    ENNReal.ofReal_toReal hfin
  let R : ℝ := D + η / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hshort : riemannianEDistOf L.metric x y < ENNReal.ofReal R := by
    rw [← hDeq]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 (by dsimp [R]; linarith)
  rw [edistOf_iInf] at hshort
  simp only [iInf_lt_iff, exists_prop] at hshort
  obtain ⟨γ, hγ, hlength⟩ := hshort
  let ζ : ℝ := η / (2 * (R + 1))
  have hden : 0 < 2 * (R + 1) := by positivity
  have hζ : 0 < ζ := div_pos hη hden
  have hζeq : ζ * (2 * (R + 1)) = η := by
    dsimp [ζ]
    exact div_mul_cancel₀ η hden.ne'
  let c : ℝ := 1 + ζ
  have hc : 0 < c := by dsimp [c]; linarith
  have hδ : 0 < c ^ 2 - 1 := by dsimp [c]; nlinarith
  have hcR : c * R ≤ D + η := by
    have hReq : R = D + η / 2 := rfl
    dsimp [c]
    nlinarith
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  obtain ⟨d, hd, hclose⟩ :=
    L.converges (Set.range γ) (isCompact_range γ.continuous) 0 (c ^ 2 - 1) hδ
  refine ⟨d, hd, ?_⟩
  intro t ht
  have hquad : ∀ z ∈ Set.range γ, ∀ v : TangentSpace ThreeModel z,
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner z v v ≤
        c ^ 2 * L.metric.inner z v v := by
    intro z hz v
    have h := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le L.metric
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) z
      (hclose t ht z hz).le v).2
    have hcoeff : (1 : ℝ) + (c ^ 2 - 1) = c ^ 2 := by ring
    simpa only [hcoeff] using h
  have hmap : ContMDiff (𝓡∂ 1) ThreeModel 1 (γ.map continuous_subtype_val) :=
    (contMDiff_subtype_val (I := ThreeModel) (U := G.terminalRegularOpen)).comp hγ
  have hdist : riemannianEDistOf (G.flow.base.metric t) x.val y.val ≤
      ∫⁻ z, ENNReal.ofReal (Real.sqrt
        ((G.flow.base.metric t).inner ((γ.map continuous_subtype_val) z)
          (mfderiv (𝓡∂ 1) ThreeModel (γ.map continuous_subtype_val) z 1)
          (mfderiv (𝓡∂ 1) ThreeModel (γ.map continuous_subtype_val) z 1))) := by
    rw [edistOf_iInf]
    exact iInf_le_of_le (γ.map continuous_subtype_val) (iInf_le_of_le hmap le_rfl)
  calc
    riemannianEDistOf (G.flow.base.metric t) x.val y.val ≤
        ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (Real.sqrt
          (L.metric.inner (γ z) (mfderiv (𝓡∂ 1) ThreeModel γ z 1) (mfderiv (𝓡∂ 1) ThreeModel γ z 1))) :=
      hdist.trans (path_integral_subtype_le G.terminalRegularOpen
        (G.flow.base.metric t) L.metric γ hγ hc.le hquad)
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal R := mul_le_mul' le_rfl hlength.le
    _ = ENNReal.ofReal (c * R) := (ENNReal.ofReal_mul hc.le).symm
    _ ≤ ENNReal.ofReal (D + η) := ENNReal.ofReal_le_ofReal hcR
    _ = riemannianEDistOf L.metric x y + ENNReal.ofReal η := by
      rw [ENNReal.ofReal_add hD hη.le, hDeq]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
