import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutMultiNull
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.BallEstimate.SourceTailControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinUnique
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.InjectivityExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds

noncomputable section
open Set Manifold Bundle MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lExpPartial_on_open_nonconjugate_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) {τ : ℝ}
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ Z ∈ U, (Z, τ) ∈ lExpPosDom S T x)
    (hnconj : ∀ Z ∈ U, ¬ IsLConjugate S T x Z τ)
    (hinj : Set.InjOn (fun Z : E => lExp S T x Z τ) U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = U ∧ Φ.target = (fun Z : E => lExp S T x Z τ) '' U ∧
      EqOn Φ (fun Z : E => lExp S T x Z τ) U := by
  exact Geometry.Riemannian.exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
    (fun Z => lExp_localDiffeo S hS T x Z.val τ (hdom Z.val Z.property) (hnconj Z.val Z.property)) hU hinj

omit [NeZero (Module.finrank ℝ E)] in
theorem lintegral_lReducedJacobian_eq_on_nonconjugate_family [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) {τ : ℝ}
    {U A : Set E} (hU : IsOpen U)
    (hdom : ∀ Z ∈ U, (Z, τ) ∈ lExpPosDom S T x)
    (hnconj : ∀ Z ∈ U, ¬ IsLConjugate S T x Z τ)
    (hinj : Set.InjOn (fun Z : E => lExp S T x Z τ) U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z τ * lSourceDensity S T x)
      ∂modelHaar (E := E)) =
      ∫⁻ y in (fun Z : E => lExp S T x Z τ) '' A,
        ENNReal.ofReal (redDensity S T x y τ)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - τ)) := by
  obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_nonconjugate_family
    S hS T x hU hdom hnconj hinj
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { Φ.toPartialEquiv with
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hAsource : A ⊆ Ψ.source := by change A ⊆ Φ.source; rwa [hsource]
  have hΨeq : EqOn Ψ (fun Z : E => lExp S T x Z τ) Ψ.source := by
    intro Z hZ
    exact hEq (hsource ▸ hZ)
  have himage : Ψ '' A = (fun Z : E => lExp S T x Z τ) '' A :=
    image_congr (fun Z hZ => hΨeq (hAsource hZ))
  rw [← himage, riemVol_param_lint (S.base.metric (T - τ)) Ψ
    (fun y => ENNReal.ofReal (redDensity S T x y τ)) hA hAsource]
  apply setLIntegral_congr_fun hA
  intro Z hZ
  have hdomZ := hdom Z (hAU hZ)
  have hnc := hnconj Z (hAU hZ)
  dsimp only
  rw [paramDensity_eq_lExpDensity_of_eqOn S T x τ Ψ hΨeq Z (hAsource hZ),
    hΨeq (hAsource hZ), ← ENNReal.ofReal_mul (lExpDensity_pos_of_nonconj S T x Z τ hdomZ hnc).le]
  exact congrArg ENNReal.ofReal (lRedJac_mul_src_of_nonconj S T x Z τ hdomZ hnc)


theorem lintegral_redDensity_image_lExp_le_one_at_minimizing_time_of_bdd [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) {τ : ℝ}
    {U A : Set E} (hU : IsOpen U)
    (hmin : ∀ Z ∈ U, (Z, τ) ∈ lMinDomain S T x)
    (hnconj : ∀ Z ∈ U, ¬ IsLConjugate S T x Z τ)
    (hinj : Set.InjOn (fun Z : E => lExp S T x Z τ) U)
    (hbdd : ∀ Z ∈ U, BddBelow {a : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt τ) = lExp S T x Z τ ∧ lRegularizedAction S T γ 0 (Real.sqrt τ) = a})
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ y in (fun Z : E => lExp S T x Z τ) '' A,
      ENNReal.ofReal (redDensity S T x y τ)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ))) ≤ 1 := by
  rw [← lintegral_lReducedJacobian_eq_on_nonconjugate_family S hS T x hU
    (fun Z hZ => ((mem_lMinDomain S T x Z τ).mp (hmin Z hZ)).1) hnconj hinj hA hAU]
  calc
    _ ≤ ∫⁻ Z in A, ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
      apply setLIntegral_mono' hA
      intro Z hZ
      apply ENNReal.ofReal_le_ofReal
      rw [lSourceGaussian_eq_metric_norm]
      have hh := mul_le_mul_of_nonneg_right
        (lReducedJacobian_le_gaussian_at_minimizing_time_of_bdd S hS T x (hmin Z (hAU hZ))
          (hnconj Z (hAU hZ)) (hbdd Z (hAU hZ))) (lSourceDensity_pos S T x).le
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
    _ ≤ ∫⁻ Z, ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := setLIntegral_le_lintegral _ _
    _ = 1 := lSourceGaussian_mass S T x

end DifferentialGeometry.PDE.RicciFlow.Perelman
end

noncomputable section

open Set Manifold Bundle MeasureTheory
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [dim_nonzero : NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lExpPartial_on_open_minimizing_family_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    {U : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hcost : ∀ Z ∈ U, BddBelow {r : ℝ | ∃ α : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧ α (Real.sqrt σ) = lExp S T x Z σ ∧
        lRegularizedAction S T α 0 (Real.sqrt σ) = r}) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = U ∧ Φ.target = (fun Z : E => lExp S T x Z τ) '' U ∧
      EqOn Φ (fun Z : E => lExp S T x Z τ) U := by
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (fun Z : E => lExp S T x Z τ) U := by
    intro Z
    have hdom := lExpPosDom_down S T x Z.val
      ((mem_lMinDomain S T x Z.val σ).mp (hmin Z.val Z.property)).1 hτ hτσ.le
    have hnc := lMinVec_nconj_lt_of_bdd S hS T x (hmin Z.val Z.property) hτσ (hcost Z.val Z.property)
    exact lExp_localDiffeo S hS T x Z.val τ hdom hnc
  have hinj : InjOn (fun Z : E => lExp S T x Z τ) U := by
    intro Z hZ W hW heq
    have hWτ := lMinDomain_down_of_bdd S hS T x W (hmin W hW) hτ hτσ.le
      (lRegularizedCosts_prefix_bdd_of_min S hS T x W (hmin W hW) hτ hτσ.le (hcost W hW)) (hcost W hW)
    exact (lMinVec_unique_lt_of_bdd S hS T x (hmin Z hZ) hτσ hWτ heq.symm (hcost Z hZ)).symm
  exact Geometry.Riemannian.exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
    hlocal hU hinj




attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hcost : ∀ Z ∈ U, BddBelow {r : ℝ | ∃ α : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧ α (Real.sqrt σ) = lExp S T x Z σ ∧
        lRegularizedAction S T α 0 (Real.sqrt σ) = r})
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z τ * lSourceDensity S T x)
      ∂modelHaar (E := E)) =
      ∫⁻ y in (fun Z : E => lExp S T x Z τ) '' A,
        ENNReal.ofReal (redDensity S T x y τ)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - τ)) := by
  obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_minimizing_family_of_bdd
    S hS T x hτ hτσ hU hmin hcost
  have hinj : Set.InjOn (fun Z : E => lExp S T x Z τ) U := by
    intro Z hZ W hW heq
    apply Φ.injOn (hsource.symm ▸ hZ) (hsource.symm ▸ hW)
    rw [hEq hZ, hEq hW]
    exact heq
  apply lintegral_lReducedJacobian_eq_on_nonconjugate_family S hS T x hU ?_ ?_ hinj hA hAU
  · intro Z hZ
    exact lExpPosDom_down S T x Z ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1 hτ hτσ.le
  · intro Z hZ
    exact lMinVec_nconj_lt_of_bdd S hS T x (hmin Z hZ) hτσ (hcost Z hZ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_redDensity_image_lExp_anti_on_minimizing_family_of_bdd [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hτ₂σ : τ₂ < σ)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hcost : ∀ Z ∈ U, BddBelow {r : ℝ | ∃ α : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧ α (Real.sqrt σ) = lExp S T x Z σ ∧
        lRegularizedAction S T α 0 (Real.sqrt σ) = r})
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ y in (fun Z : E => lExp S T x Z τ₂) '' A,
      ENNReal.ofReal (redDensity S T x y τ₂)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₂))) ≤
    ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' A,
      ENNReal.ofReal (redDensity S T x y τ₁)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  rw [← lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd S hS T x (hτ₁.trans_le hτ) hτ₂σ hU hmin hcost hA hAU,
    ← lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd S hS T x hτ₁ (hτ.trans_lt hτ₂σ) hU hmin hcost hA hAU]
  apply setLIntegral_mono' hA
  intro Z hZ
  have hmono := lRedJac_antitoneOn_of_bdd S hS T x (hmin Z (hAU hZ)) (hcost Z (hAU hZ))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (hmono ⟨hτ₁, hτ.trans_lt hτ₂σ⟩ ⟨hτ₁.trans_le hτ, hτ₂σ⟩ hτ)
    (lSourceDensity_pos S T x).le)



attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lExpPartial_on_open_minimizing_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ K : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    (hRm : ∀ t ∈ Icc (T - σ) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {U : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = U ∧ Φ.target = (fun Z : E => lExp S T x Z τ) '' U ∧
      EqOn Φ (fun Z : E => lExp S T x Z τ) U := by
  let _ := dim_nonzero
  apply exists_lExpPartial_on_open_minimizing_family_of_bdd S hS T x hτ hτσ hU hmin
  intro Z hZ
  have hdom := ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt σ) le_rfl (Real.sqrt_nonneg σ)
    (by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hback : T - t ≤ σ := by linarith [ht.1, Real.sq_sqrt (hτ.trans hτσ).le]
      have hh := lExpPosDom_regularity S T x Z hdom ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
      simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hh)
    (by simpa only [Real.sq_sqrt (hτ.trans hτσ).le] using hRm) x (lExp S T x Z σ)

variable [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_lReducedJacobian_eq_on_minimizing_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ K : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    (hRm : ∀ t ∈ Icc (T - σ) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z τ * lSourceDensity S T x)
      ∂modelHaar (E := E)) =
      ∫⁻ y in (fun Z : E => lExp S T x Z τ) '' A,
        ENNReal.ofReal (redDensity S T x y τ)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - τ)) := by
  let _ := dim_nonzero
  apply lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd S hS T x hτ hτσ hU hmin _ hA hAU
  intro Z hZ
  have hdom := ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt σ) le_rfl (Real.sqrt_nonneg σ)
    (by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hback : T - t ≤ σ := by linarith [ht.1, Real.sq_sqrt (hτ.trans hτσ).le]
      have hh := lExpPosDom_regularity S T x Z hdom ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
      simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hh)
    (by simpa only [Real.sq_sqrt (hτ.trans hτσ).le] using hRm) x (lExp S T x Z σ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_redDensity_image_lExp_anti_on_minimizing_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ₁ τ₂ K : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hτ₂σ : τ₂ < σ)
    (hRm : ∀ t ∈ Icc (T - σ) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ y in (fun Z : E => lExp S T x Z τ₂) '' A,
      ENNReal.ofReal (redDensity S T x y τ₂)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₂))) ≤
    ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' A,
      ENNReal.ofReal (redDensity S T x y τ₁)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  apply lintegral_redDensity_image_lExp_anti_on_minimizing_family_of_bdd S hS T x hτ₁ hτ hτ₂σ hU hmin _ hA hAU
  intro Z hZ
  have hσ := hτ₁.trans_le (hτ.trans hτ₂σ.le)
  have hdom := ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt σ) le_rfl (Real.sqrt_nonneg σ)
    (by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hback : T - t ≤ σ := by linarith [ht.1, Real.sq_sqrt hσ.le]
      have hh := lExpPosDom_regularity S T x Z hdom ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
      simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hh)
    (by simpa only [Real.sq_sqrt hσ.le] using hRm) x (lExp S T x Z σ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem measure_mul_exp_le_redDensity_image_of_minimizing_action_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ₁ τ₂ K L : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hτ₂σ : τ₂ < σ)
    (hRm : ∀ t ∈ Icc (T - σ) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hA : MeasurableSet A) (hAU : A ⊆ U)
    (haction : ∀ Z ∈ A,
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ₂) ≤ L) :
    riemannianVolumeMeasure I M (S.base.metric (T - τ₂))
        ((fun Z : E => lExp S T x Z τ₂) '' A) *
      ENNReal.ofReal (Real.exp (-L / (2 * Real.sqrt τ₂) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log τ₂ -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) ≤
    ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' A,
      ENNReal.ofReal (redDensity S T x y τ₁)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have hmeas : MeasurableSet ((fun Z : E => lExp S T x Z τ₂) '' A) := by
    obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_minimizing_family
      S hS T x hτ₂ hτ₂σ hRm hU hmin
    let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
      { Φ.toPartialEquiv with
        open_source := Φ.open_source
        open_target := Φ.open_target
        contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
        contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
    have himage : Ψ '' A = (fun Z : E => lExp S T x Z τ₂) '' A :=
      image_congr (fun Z hZ => hEq (hAU hZ))
    rw [← himage]
    exact measurableSet_image_param_global Ψ hA (by change A ⊆ Φ.source; rwa [hsource])
  have hlen (Z : E) (hZ : Z ∈ A) : redLength S T x (lExp S T x Z τ₂) τ₂ ≤
      L / (2 * Real.sqrt τ₂) := by
    have hm := lMinDomain_down_of_rm S hS K T x Z (hmin Z (hAU hZ)) hτ₂ hτ₂σ.le hRm
    have hcost := ((mem_lMinDomain S T x Z τ₂).mp hm).2
    have hact : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ₂) =
        lCost S T x (lExp S T x Z τ₂) τ₂ := by
      rw [← hcost]
      change _ = lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 τ₂
      exact (lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ₂.le).symm
    unfold redLength
    exact div_le_div_of_nonneg_right (hact ▸ haction Z hZ) (by positivity)
  let d := ENNReal.ofReal (Real.exp (-L / (2 * Real.sqrt τ₂) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log τ₂ -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
  have hmass : riemannianVolumeMeasure I M (S.base.metric (T - τ₂))
      ((fun Z : E => lExp S T x Z τ₂) '' A) * d ≤
      ∫⁻ y in (fun Z : E => lExp S T x Z τ₂) '' A,
        ENNReal.ofReal (redDensity S T x y τ₂)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₂)) := by
    rw [mul_comm, ← setLIntegral_const]
    apply setLIntegral_mono' hmeas
    rintro y ⟨Z, hZ, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := hlen Z hZ
    change -L / (2 * Real.sqrt τ₂) - _ - _ ≤ -redLength S T x (lExp S T x Z τ₂) τ₂ - _ - _
    rw [neg_div]
    linarith
  exact hmass.trans (lintegral_redDensity_image_lExp_anti_on_minimizing_family
    S hS T x hτ₁ hτ hτ₂σ hRm hU hmin hA hAU)


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_low_action_minimizing_patch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ K L : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    (hRm : ∀ t ∈ Icc (T - σ) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {U : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    {Z₀ : E} (hZ₀ : Z₀ ∈ U)
    (haction : lRegularizedAction S T (lRegularizedCurve S T x Z₀) 0 (Real.sqrt τ) < L) :
    ∃ V : Set E, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ U ∧
      (∀ Z ∈ V, lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ) < L) ∧
      IsOpen ((fun Z : E => lExp S T x Z τ) '' V) ∧
      0 < riemannianVolumeMeasure I M (S.base.metric (T - τ))
        ((fun Z : E => lExp S T x Z τ) '' V) := by
  let f := fun Z : E => lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ)
  have hcont : ContinuousOn f U := by
    intro Z hZ
    have hdom := lExpPosDom_down S T x Z
      ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1 hτ hτσ.le
    have hh := (hasFDerivAt_lRegularizedAction_lRegularizedCurve_sqrt S hS T x Z hdom).continuousAt
    have hpair : ContinuousAt (fun W : E => (W, τ)) Z := continuousAt_id.prodMk continuousAt_const
    have hcomp := hh.comp (f := fun W : E => (W, τ)) hpair
    exact hcomp.continuousWithinAt
  let V := U ∩ f ⁻¹' Iio L
  have hV : IsOpen V := hcont.isOpen_inter_preimage hU isOpen_Iio
  have hZV : Z₀ ∈ V := ⟨hZ₀, haction⟩
  have hVU : V ⊆ U := inter_subset_left
  obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_minimizing_family
    S hS T x hτ hτσ hRm hU hmin
  have himage : Φ '' V = (fun Z : E => lExp S T x Z τ) '' V :=
    image_congr (fun Z hZ => hEq (hVU hZ))
  have hVo : IsOpen ((fun Z : E => lExp S T x Z τ) '' V) := by
    rw [← himage]
    exact Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV (by change V ⊆ Φ.source; rwa [hsource])
  let _ : (riemannianVolumeMeasure I M (S.base.metric (T - τ))).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure _
  exact ⟨V, hV, hZV, hVU, (fun _ hZ => hZ.2), hVo, hVo.measure_pos _ ⟨_, ⟨Z₀, hZV, rfl⟩⟩⟩


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_low_action_lExp_patch [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ L : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    {Z₀ : E} (hZ₀ : Z₀ ∈ lInjDomain S T x σ)
    (haction : lRegularizedAction S T (lRegularizedCurve S T x Z₀) 0 (Real.sqrt τ) < L) :
    ∃ V : Set E, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ lInjDomain S T x σ ∧
      (∀ Z ∈ V, lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ) < L) ∧
      IsOpen ((fun Z : E => lExp S T x Z τ) '' V) ∧
      0 < riemannianVolumeMeasure I M (S.base.metric (T - τ))
        ((fun Z : E => lExp S T x Z τ) '' V) ∧
      ∀ τ₁ : ℝ, 0 < τ₁ → τ₁ ≤ τ →
        riemannianVolumeMeasure I M (S.base.metric (T - τ))
            ((fun Z : E => lExp S T x Z τ) '' V) *
          ENNReal.ofReal (Real.exp (-L / (2 * Real.sqrt τ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log τ -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) ≤
        ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' V,
          ENNReal.ofReal (redDensity S T x y τ₁)
          ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  have hσ : 0 < σ := hτ.trans hτσ
  have hmin : ∀ Z ∈ lInjDomain S T x σ, (Z, σ) ∈ lMinDomain S T x := by
    rintro Z ⟨σ', hσσ', hmin'⟩
    exact lMinDomain_down S hS T x Z hmin' hσ hσσ'.le
  have hdom := ((mem_lMinDomain S T x Z₀ σ).mp (hmin Z₀ hZ₀)).1
  have hreg : Icc (T - σ) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ σ := by linarith [ht.1]
    have hclock := lExpPosDom_regularity S T x Z₀ hdom
      (show Real.sqrt (T - t) ∈ Icc 0 (Real.sqrt σ) from
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩)
    rwa [Real.sq_sqrt hnonneg, sub_sub_cancel] at hclock
  obtain ⟨K, _, hRm⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS hreg
  obtain ⟨V, hV, hZV, hVU, hact, hopen, hpos⟩ := exists_open_low_action_minimizing_patch
    S hS T x hτ hτσ hRm (lInj_isOpen S hS T x σ) hmin hZ₀ haction
  refine ⟨V, hV, hZV, hVU, hact, hopen, hpos, ?_⟩
  intro τ₁ hτ₁ hτ₁τ
  exact measure_mul_exp_le_redDensity_image_of_minimizing_action_bound S hS T x hτ₁ hτ₁τ hτσ
    hRm (lInj_isOpen S hS T x σ) hmin hV.measurableSet hVU (fun Z hZ => (hact Z hZ).le)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [SigmaCompactSpace M] in
theorem lintegral_lReducedJacobian_le_one_on_minimizing_family_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {sigma tau : ℝ} (htau : 0 < tau) (hlt : tau < sigma)
    {A : Set E} (hA : MeasurableSet A)
    (hmin : ∀ Z ∈ A, (Z, sigma) ∈ lMinDomain S T x)
    (hbdd : ∀ Z ∈ A, BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
      ∂modelHaar (E := E)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ Z in A, ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      setLIntegral_mono' hA (fun Z hZ =>
        lReducedJacobian_source_le_of_bdd S hS T x (hmin Z hZ) htau hlt (hbdd Z hZ))
    _ ≤ ∫⁻ Z, ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      setLIntegral_le_lintegral _ _
    _ = 1 := lSourceGaussian_mass S T x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_redDensity_image_lExp_le_one_on_minimizing_family_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {sigma tau : ℝ} (htau : 0 < tau) (hlt : tau < sigma)
    {U A : Set E} (hU : IsOpen U)
    (hmin : ∀ Z ∈ U, (Z, sigma) ∈ lMinDomain S T x)
    (hbdd : ∀ Z ∈ U, BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r})
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ y in (fun Z : E => lExp S T x Z tau) '' A,
      ENNReal.ofReal (redDensity S T x y tau)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - tau))) ≤ 1 := by
  rw [← lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd S hS T x htau hlt hU hmin hbdd hA hAU]
  exact lintegral_lReducedJacobian_le_one_on_minimizing_family_of_bdd S hS T x htau hlt hA
    (fun Z hZ => hmin Z (hAU hZ)) (fun Z hZ => hbdd Z (hAU hZ))

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

open Set Manifold Bundle MeasureTheory Filter
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_low_action_lExp_patch_at_regular_pole [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (hT : T ∈ D.regular) {L : ℝ} (hL : 0 < L) :
    ∃ σ τ : ℝ, 0 < τ ∧ τ < σ ∧
      ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ lInjDomain S T x σ ∧
      (∀ Z ∈ V, lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ) < L) ∧
      IsOpen ((fun Z : E => lExp S T x Z τ) '' V) ∧
      0 < riemannianVolumeMeasure I M (S.base.metric (T - τ))
        ((fun Z : E => lExp S T x Z τ) '' V) ∧
      ∀ τ₁ : ℝ, 0 < τ₁ → τ₁ ≤ τ →
        riemannianVolumeMeasure I M (S.base.metric (T - τ))
            ((fun Z : E => lExp S T x Z τ) '' V) *
          ENNReal.ofReal (Real.exp (-L / (2 * Real.sqrt τ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log τ -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) ≤
        ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' V,
          ENNReal.ofReal (redDensity S T x y τ₁)
          ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  have hinj := eventually_mem_lInjDomain S hS T x (0 : E) hT
  obtain ⟨σ, hσinj, hσ⟩ := (hinj.and (show ∀ᶠ σ : ℝ in 𝓝[>] 0, 0 < σ from self_mem_nhdsWithin)).exists
  have hquot := tendsto_lRegularizedAction_div_at_zero S hS T x (0 : E) hT
  have hid : Tendsto (fun b : ℝ => 2 * b) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    have hh : Continuous (fun b : ℝ => (2 : ℝ) * b) := continuous_const.mul continuous_id
    simpa only [mul_zero] using (hh.tendsto (0 : ℝ)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hact : Tendsto (fun b : ℝ => lRegularizedAction S T (lRegularizedCurve S T x 0) 0 b)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    have hh := hquot.mul hid
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    change 0 < b at hb
    exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hb.ne')
  have hsmall := hact.eventually_lt_const hL
  have hbound : ∀ᶠ b : ℝ in 𝓝[>] 0, b < Real.sqrt σ :=
    (eventually_lt_nhds (Real.sqrt_pos.mpr hσ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hbact, hbsmall, hbpos⟩ := (hsmall.and (hbound.and (show ∀ᶠ b : ℝ in 𝓝[>] 0, 0 < b from self_mem_nhdsWithin))).exists
  have hbsq : b ^ 2 < σ := by
    have hs := Real.sq_sqrt hσ.le
    nlinarith
  refine ⟨σ, b ^ 2, sq_pos_of_pos hbpos, hbsq, ?_⟩
  apply exists_open_low_action_lExp_patch S hS T x (sq_pos_of_pos hbpos) hbsq hσinj
  rw [Real.sqrt_sq hbpos.le]
  exact hbact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_redDensity_image_lExp_anti_of_scalar_lower
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ₁ τ₂ B : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hτ₂σ : τ₂ < σ)
    (hscalar : ∀ t ∈ Icc (T - σ) T, ∀ z : M, -B ≤ S.scalar t z)
    {U A : Set E} (hU : IsOpen U) (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (∫⁻ y in (fun Z : E => lExp S T x Z τ₂) '' A,
      ENNReal.ofReal (redDensity S T x y τ₂)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₂))) ≤
    ∫⁻ y in (fun Z : E => lExp S T x Z τ₁) '' A,
      ENNReal.ofReal (redDensity S T x y τ₁)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ₁)) := by
  apply lintegral_redDensity_image_lExp_anti_on_minimizing_family_of_bdd S hS T x
    hτ₁ hτ hτ₂σ hU hmin _ hA hAU
  intro Z hZ
  have hσ : 0 < σ := hτ₁.trans_le (hτ.trans hτ₂σ.le)
  have hdom := ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1
  apply lRegularizedCosts_bdd_of_scalar_lower S hS T (Real.sqrt_nonneg σ)
  · intro t ht
    exact D.regular_subset (lExpPosDom_regularity S T x Z hdom ht)
  · intro t ht z
    have ht2 : t ^ 2 ≤ σ := (Real.le_sqrt ht.1.le hσ.le).mp ht.2.le
    exact hscalar (T - t ^ 2) ⟨by linarith, sub_le_self _ (sq_nonneg t)⟩ z

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Filter Bundle MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_redDensity_le_one_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {τ A : ℝ} (hτ : 0 < τ) (hreg : Icc (T - τ) T ⊆ D.regular)
    (K : Set M) (hK : IsCompact K) (U : Set M) (hU : IsOpen U)
    (hbdd : ∀ y : M, BddBelow {a : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧
      α (Real.sqrt τ) = y ∧ lRegularizedAction S T α 0 (Real.sqrt τ) = a})
    (hseed : ∀ y ∈ U, ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧
      α (Real.sqrt τ) = y ∧ lRegularizedAction S T α 0 (Real.sqrt τ) < A)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x → α (Real.sqrt τ) ∈ U →
      lRegularizedAction S T α 0 (Real.sqrt τ) ≤ A → MapsTo α (Icc 0 (Real.sqrt τ)) K) :
    (∫⁻ y in U, ENNReal.ofReal (redDensity S T x y τ)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - τ))) ≤ 1 := by
  let b := Real.sqrt τ
  have hb : 0 < b := Real.sqrt_pos.mpr hτ
  have hb2 : b ^ 2 = τ := Real.sq_sqrt hτ.le
  have hclock : ∀ r ∈ Icc (0 : ℝ) b, T - r ^ 2 ∈ D.regular := by
    intro r hr
    have hr2 : r ^ 2 ≤ τ := by
      have hh := (sq_le_sq₀ hr.1 hb.le).mpr hr.2
      simpa only [hb2] using hh
    exact hreg ⟨by linarith, sub_le_self _ (sq_nonneg r)⟩
  have hexists (y : M) (hy : y ∈ U) : ∃ Z : TangentSpace I x,
      (Z, τ) ∈ lMinDomain S T x ∧ lExp S T x Z τ = y := by
    obtain ⟨α, hα, hα0, hαb, hαact⟩ := hseed y hy
    obtain ⟨η, hη, hη0, hηb, _, hmin⟩ := exists_lRegularizedMinC1_of_compact_action_sublevel S hS T hb hclock
      x y α hα hα0 hαb K hK (fun δ hδ hδ0 hδb hδact =>
        hconf δ hδ hδ0 (hδb.symm ▸ hy) (hδact.trans hαact.le))
    have hm : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = η 0 → δ b = η b →
        lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b :=
      fun δ hδ hδ0 hδb => hmin δ hδ (hδ0.trans hη0) (hδb.trans hηb)
    cases hη0
    obtain ⟨Z, hZ, hZend, _, _⟩ := exists_lMinimizingVector_of_minimal S hS T hb hclock η hη hm
    rw [hb2] at hZ hZend
    exact ⟨Z, hZ, hZend.trans hηb⟩
  have hact (Z : E) (hZ : (Z, τ) ∈ lMinDomain S T x) (hy : lExp S T x Z τ ∈ U) :
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b < A := by
    obtain ⟨α, hα, hα0, hαb, hαact⟩ := hseed _ hy
    have hc := ((mem_lMinDomain S T x Z τ).mp hZ).2
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 τ = _ at hc
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ τ hτ.le] at hc
    rw [hc, lCost_eq_regularity S T x _ τ hτ.le]
    exact (lRegularizedCostC1_le_bdd S T 0 b x _ (hbdd _) α hα hα0 hαb).trans_lt hαact
  have hlip := lCost_chart_locallyLipschitzOn_of_compact_action_sublevel S hS T x hτ hreg K hK U hU hbdd
    (fun y hy => by obtain ⟨α, hα, hα0, hαb, hαact⟩ := hseed y hy; exact ⟨α, hα, hα0, hαb, hαact.le⟩) hconf
  let volume := riemannianVolumeMeasure I M (S.base.metric (T - τ))
  have hmult := lMinimizingVector_nonunique_image_null_on_of_locallyLipschitz S hS T x τ hU hlip
    (fun Z _ _ => Eventually.of_forall hbdd) (S.base.metric (T - τ))
  have hconj := lConjugateImage_null S hS T x τ (S.base.metric (T - τ))
  let V : Set E := {Z | (Z, τ) ∈ lMinDomain S T x ∧
    (∀ W : E, (W, τ) ∈ lMinDomain S T x → lExp S T x W τ = lExp S T x Z τ → W = Z) ∧
    ¬ IsLConjugate S T x Z τ ∧ lExp S T x Z τ ∈ U ∧
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b < A}
  have hV : IsOpen V := isOpen_setOf_unique_nonconjugate_minimizer_of_compact_action_sublevel
    S hS T x K hK U hU hbdd hconf
  have hinj : InjOn (fun Z : E => lExp S T x Z τ) V := by
    intro Z hZ W hW heq
    exact (hZ.2.1 W hW.1 heq.symm).symm
  have hsub : (fun Z : E => lExp S T x Z τ) '' V ⊆ U := by rintro y ⟨Z, hZ, rfl⟩; exact hZ.2.2.2.1
  have haecover : U =ᵐ[volume] (fun Z : E => lExp S T x Z τ) '' V := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hmult, measure_eq_zero_iff_ae_notMem.mp hconj] with y hym hyc
    apply propext
    constructor
    · intro hy
      obtain ⟨Z, hZ, hZy⟩ := hexists y hy
      refine ⟨Z, ⟨hZ, ?_, ?_, hZy.symm ▸ hy, hact Z hZ (hZy.symm ▸ hy)⟩, hZy⟩
      · intro W hW heq
        by_contra hWZ
        exact hym ⟨hy, Z, W, (fun h => hWZ h.symm), hZ, hW, hZy, heq.trans hZy⟩
      · exact fun hc => hyc ⟨Z, hc, hZy⟩
    · exact fun hy => hsub hy
  rw [setLIntegral_congr haecover]
  exact lintegral_redDensity_image_lExp_le_one_at_minimizing_time_of_bdd S hS T x hV
    (fun Z hZ => hZ.1) (fun Z hZ => hZ.2.2.1) hinj (fun Z _ => hbdd _) hV.measurableSet Subset.rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
end

noncomputable section
open Set Filter Bundle MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_redDensity_image_lExp_le_volume_add_gaussian_tail
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {σ τ : ℝ} (hτ : 0 < τ) (hτσ : τ < σ)
    {U A : Set E} (hU : IsOpen U) (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hnconj : ∀ Z ∈ U, ¬ IsLConjugate S T x Z σ)
    (hinj : InjOn (fun Z : E => lExp S T x Z σ) U)
    (hbdd : ∀ Z ∈ U, BddBelow {a : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt σ) = lExp S T x Z σ ∧ lRegularizedAction S T γ 0 (Real.sqrt σ) = a})
    (R : ℝ) (Q : Set M) (c : ℝ≥0∞)
    (himage : ∀ Z ∈ A, Real.sqrt ((S.base.metric T).inner x Z Z) ≤ R → lExp S T x Z τ ∈ Q)
    (hden : ∀ Z ∈ A, Real.sqrt ((S.base.metric T).inner x Z Z) ≤ R →
      ENNReal.ofReal (redDensity S T x (lExp S T x Z τ) τ) ≤ c) :
    (∫⁻ y in (fun Z : E => lExp S T x Z σ) '' A, ENNReal.ofReal (redDensity S T x y σ)
      ∂riemannianVolumeMeasure I M (S.base.metric (T - σ))) ≤
      c * riemannianVolumeMeasure I M (S.base.metric (T - τ)) Q +
        ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
  let small : Set E := {Z | Real.sqrt ((S.base.metric T).inner x Z Z) ≤ R}
  have hsmall : MeasurableSet small := by
    apply measurableSet_le _ measurable_const
    exact (Real.continuous_sqrt.comp (((S.base.metric T).inner x).continuous.clm_apply continuous_id)).measurable
  let low := A ∩ small
  have hlow : MeasurableSet low := hA.inter hsmall
  have hlowU : low ⊆ U := inter_subset_left.trans hAU
  let J := fun (s : ℝ) (Z : E) => ENNReal.ofReal (lReducedJacobian S T x Z s * lSourceDensity S T x)
  have hlowmono : (∫⁻ Z in low, J σ Z ∂modelHaar (E := E)) ≤ ∫⁻ Z in low, J τ Z ∂modelHaar (E := E) := by
    apply setLIntegral_mono' hlow
    intro Z hZ
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (lReducedJacobian_le_of_le_minimizing_time_of_bdd S hS T x (hmin Z (hlowU hZ))
        (hnconj Z (hlowU hZ)) hτ hτσ.le (hbdd Z (hlowU hZ))) (lSourceDensity_pos S T x).le
  have hlowbound : (∫⁻ Z in low, J τ Z ∂modelHaar (E := E)) ≤
      c * riemannianVolumeMeasure I M (S.base.metric (T - τ)) Q := by
    rw [lintegral_lReducedJacobian_eq_on_minimizing_family_of_bdd S hS T x hτ hτσ hU hmin hbdd hlow hlowU]
    obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_minimizing_family_of_bdd S hS T x hτ hτσ hU hmin hbdd
    let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
      { Φ.toPartialEquiv with
        open_source := Φ.open_source
        open_target := Φ.open_target
        contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
        contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
    have heqimage : Ψ '' low = (fun Z : E => lExp S T x Z τ) '' low := image_congr (fun Z hZ => hEq (hlowU hZ))
    have himagemeas : MeasurableSet ((fun Z : E => lExp S T x Z τ) '' low) := by
      rw [← heqimage]
      exact measurableSet_image_param_global Ψ hlow (by change low ⊆ Φ.source; rwa [hsource])
    have hle := setLIntegral_mono' (μ := riemannianVolumeMeasure I M (S.base.metric (T - τ))) himagemeas
      (f := fun y => ENNReal.ofReal (redDensity S T x y τ)) (g := fun _ => c) (by
        rintro y ⟨Z, hZ, rfl⟩
        exact hden Z hZ.1 hZ.2)
    rw [lintegral_const, Measure.restrict_apply_univ] at hle
    exact hle.trans (mul_le_mul_right (measure_mono (by
      rintro y ⟨Z, hZ, rfl⟩
      exact himage Z hZ.1 hZ.2)) c)
  have hhigh : (∫⁻ Z in A \ small, J σ Z ∂modelHaar (E := E)) ≤
      ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
    calc
      _ ≤ ∫⁻ Z in A \ small, ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
        apply setLIntegral_mono' (hA.diff hsmall)
        intro Z hZ
        apply ENNReal.ofReal_le_ofReal
        rw [lSourceGaussian_eq_metric_norm]
        have hh := mul_le_mul_of_nonneg_right
          (lReducedJacobian_le_gaussian_at_minimizing_time_of_bdd S hS T x (hmin Z (hAU hZ.1))
            (hnconj Z (hAU hZ.1)) (hbdd Z (hAU hZ.1))) (lSourceDensity_pos S T x).le
        simpa only [J, mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ _ := lintegral_mono_set (fun Z hZ => by
        exact lt_of_not_ge (show ¬ Real.sqrt ((S.base.metric T).inner x Z Z) ≤ R from hZ.2))
  rw [← lintegral_lReducedJacobian_eq_on_nonconjugate_family S hS T x hU
    (fun Z hZ => ((mem_lMinDomain S T x Z σ).mp (hmin Z hZ)).1) hnconj hinj hA hAU]
  change (∫⁻ Z in A, J σ Z ∂modelHaar (E := E)) ≤ _
  rw [← lintegral_inter_add_sdiff (J σ) A hsmall]
  exact add_le_add (hlowmono.trans hlowbound) hhigh

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
