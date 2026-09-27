import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain

set_option autoImplicit false
noncomputable section
open Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedCurve_eqOn_of_minimal
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b : ℝ} (hb : 0 < b) (hreg : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.regular)
    (η : ℝ → M) (hη : ContMDiff 𝓘(ℝ, ℝ) I 1 η)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = η 0 → δ b = η b →
      lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b) :
    ∃ Z : TangentSpace I (η 0), b ∈ lRegularizedDomain S T (η 0) Z ∧
      EqOn (lRegularizedCurve S T (η 0) Z) η (Icc 0 b) := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let K := η '' Icc 0 b
  have hK : IsCompact K := isCompact_Icc.image hη.continuous
  obtain ⟨m, t, p, u, htmono, ht0, htlast, hsrc, hrep, _⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 b (lRegularizedAction S T η 0 b) hb.le
      (fun _ : ℕ => η) (fun _ => hη.contMDiffOn) K hK
      (fun _ s hs => ⟨s, hs, rfl⟩) (fun _ => le_rfl) η
      (by intro U hU; exact Eventually.of_forall fun _ _ => mem_uniformity_of_eq hU rfl) (fun s hs => D.regular_subset (hreg s hs))
  have hsol := lMinCurve_regularity S hS T 0 b hb t htmono ht0 htlast p η hη.continuous u
    hsrc hrep hreg hmin
  obtain ⟨α, hαeq, e, he, hαsol⟩ := exists_lRegularizedExtOn S hS T 0 b hb η hη.contMDiffOn hreg hsol
  have hα0 : α 0 = η 0 := hαeq ⟨le_rfl, hb.le⟩
  let Z : TangentSpace I (η 0) := (2 : ℝ)⁻¹ • lVelocity (I := I) α 0
  have hvel : lVelocity (I := I) α 0 = 2 • Z := by
    have hh : lVelocity (I := I) α 0 = (2 : ℝ) • Z := by
      simp only [Z]
      exact (smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0) _).symm
    exact hh.trans (Nat.cast_smul_eq_nsmul ℝ 2 Z)
  have hcurve : IsLRegularizedCurveOn S T α (Ioo (-e) (b + e)) (η 0) Z := by
    refine ⟨hα0, hvel, ?_⟩
    simpa only [IsLRegularizedGeodesicOn, zero_sub] using hαsol
  have h0 : (0 : ℝ) ∈ Ioo (-e) (b + e) := by constructor <;> linarith
  have hbe : b ∈ Ioo (-e) (b + e) := by constructor <;> linarith
  refine ⟨Z, ⟨α, Ioo (-e) (b + e), isOpen_Ioo, isPreconnected_Ioo, h0, hbe, hcurve⟩, ?_⟩
  exact (lRegularizedCurve_eqIcc S hS T b e hb.le he hcurve).trans hαeq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lMinimizingVector_of_minimal
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b : ℝ} (hb : 0 < b) (hreg : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.regular)
    (η : ℝ → M) (hη : ContMDiff 𝓘(ℝ, ℝ) I 1 η)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = η 0 → δ b = η b →
      lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b) :
    ∃ Z : TangentSpace I (η 0), (Z, b ^ 2) ∈ lMinDomain S T (η 0) ∧
      lExp S T (η 0) Z (b ^ 2) = η b ∧
      EqOn (lRegularizedCurve S T (η 0) Z) η (Icc 0 b) ∧
      lRegularizedAction S T (lRegularizedCurve S T (η 0) Z) 0 b = lRegularizedAction S T η 0 b := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨Z, hbDom, heq⟩ := exists_lRegularizedCurve_eqOn_of_minimal S hS T hb hreg η hη hmin
  have hsqrt : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
  have hdom : (Z, b ^ 2) ∈ lExpPosDom S T (η 0) := by
    apply (mem_lExpPosDom S T (η 0) Z (b ^ 2)).mpr
    exact ⟨sq_pos_of_pos hb, sq_nonneg b, hsqrt.symm ▸ hbDom⟩
  have hExp : lExp S T (η 0) Z (b ^ 2) = η b := by
    simpa only [lExp, hsqrt] using heq ⟨hb.le, le_rfl⟩
  have hact : lRegularizedAction S T (lRegularizedCurve S T (η 0) Z) 0 b = lRegularizedAction S T η 0 b := by
    apply lRegularizedAction_congr
    intro s hs
    rw [uIoo_of_le hb.le] at hs
    exact heq (Ioo_subset_Icc_self hs)
  have hcost : lRegularizedCostC1 S T 0 b (η 0) (η b) = lRegularizedAction S T η 0 b := by
    let costs : Set ℝ := {c | ∃ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ ∧
      δ 0 = η 0 ∧ δ b = η b ∧ lRegularizedAction S T δ 0 b = c}
    have hmem : lRegularizedAction S T η 0 b ∈ costs := ⟨η, hη, rfl, rfl, rfl⟩
    have hlow : ∀ c ∈ costs, lRegularizedAction S T η 0 b ≤ c := by
      rintro c ⟨δ, hδ, hzero, hend, rfl⟩
      exact hmin δ hδ hzero hend
    exact le_antisymm (csInf_le ⟨_, hlow⟩ hmem) (le_csInf ⟨_, hmem⟩ hlow)
  have hlength : lLength S T (fun r : ℝ => lExp S T (η 0) Z r) 0 (b ^ 2) =
      lCost S T (η 0) (lExp S T (η 0) Z (b ^ 2)) (b ^ 2) := by
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T (η 0) Z)) 0 (b ^ 2) = _
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ _ (sq_nonneg b),
      hsqrt, hact, hExp, lCost_eq_regularity S T _ _ _ (sq_nonneg b), hsqrt, hcost]
  exact ⟨Z, ⟨hdom, hlength⟩, hExp, heq, hact⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
