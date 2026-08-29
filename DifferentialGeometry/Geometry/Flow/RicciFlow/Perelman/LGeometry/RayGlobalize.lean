import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.JacobiSmooth

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_isReg
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    IsLRegCurveOn S T (lRegCurve S T x Z)
      (Set.uIcc (0 : Real) b) x Z := by
  have h0dom : (0 : Real) ∈ lRegDomain S T x Z :=
    lRegDomain_seg S T x Z hb le_rfl hb0.le
  have hT : T ∈ D.regular := by
    simpa using lRegDomain_reg S T x Z h0dom
  refine ⟨lRegCurve_zero S T x Z, ?_, ?_⟩
  · have htwo : (2 : Real) • Z = (2 : Nat) • Z := by
      rw [two_smul, two_nsmul]
    with_unfolding_all exact
      ((lRegCurve_vel_zero S hS T x Z hT).trans htwo)
  intro s hs
  have hsIcc : s ∈ Set.Icc (0 : Real) b := by
    simpa only [Set.uIcc_of_le hb0.le] using hs
  have hsdom : s ∈ lRegDomain S T x Z :=
    lRegDomain_seg S T x Z hb hsIcc.1 hsIcc.2
  obtain ⟨K, hKopen, hKconn, h0K, hsK, hchosen⟩ :=
    lRegChosen_spec S T x Z hsdom
  have heqOn : Set.EqOn (lRegCurve S T x Z)
      (lRegChosen S T x Z hsdom) K :=
    lRegCurve_eqOn S hS T hKopen hKconn h0K hchosen
  have heq : lRegCurve S T x Z =ᶠ[nhds s]
      lRegChosen S T x Z hsdom :=
    Filter.eventuallyEq_of_mem (hKopen.mem_nhds hsK) heqOn
  exact lRegData_congr S T s heq (hchosen.2.2 s hsK)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lReg_clamp
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ∃ rho : Real → Real, ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc (0 : Real) b) ∧
      (∀ s ∈ Set.Icc (0 : Real) b, HasDerivAt rho 1 s) ∧
      ∀ s : Real, rho s ∈ lRegDomain S T x Z := by
  have hseg : Set.Icc (0 : Real) b ⊆ lRegDomain S T x Z := by
    intro s hs
    exact lRegDomain_seg S T x Z hb hs.1 hs.2
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open
      (lRegDomain_isOpen S T x Z) hseg
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp
      (0 : Real) b margin hb0 hmargin
  refine ⟨rho, hrho, ?_, hrho_deriv, fun s ↦ hbuffer ?_⟩
  · intro s hs
    simpa only [id_eq] using hrho_id s hs
  · by_cases hs0 : rho s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (rho s) 0 margin
        (Set.Icc (0 : Real) b) ⟨le_rfl, hb0.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      linarith [(hrho_range s).1]
    · by_cases hsb : rho s ≤ b
      · refine Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
          (Set.Icc (0 : Real) b) ⟨(not_le.mp hs0).le, hsb⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (rho s) b margin
          (Set.Icc (0 : Real) b) ⟨hb0.le, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb).le)]
        linarith [(hrho_range s).2]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lReg_germ_in
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z)
    (U : Set Real) (hU : IsOpen U)
    (hsegU : Set.Icc (0 : Real) b ⊆ U) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < 0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc a d) ∧
      (∀ s ∈ Set.Icc a d, HasDerivAt rho 1 s) ∧
      (∀ s : Real, rho s ∈ lRegDomain S T x Z) ∧
      ∀ s : Real, rho s ∈ U := by
  let V : Set Real := lRegDomain S T x Z ∩ U
  have hVopen : IsOpen V := (lRegDomain_isOpen S T x Z).inter hU
  have hsegV : Set.Icc (0 : Real) b ⊆ V := by
    intro s hs
    exact ⟨lRegDomain_seg S T x Z hb hs.1 hs.2, hsegU hs⟩
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hVopen hsegV
  let a : Real := -(margin / 2)
  let d : Real := b + margin / 2
  let eps : Real := margin / 4
  have ha0 : a < 0 := by
    dsimp only [a]
    linarith
  have hbd : b < d := by
    dsimp only [d]
    linarith
  have had : a < d := lt_trans ha0 (hb0.trans hbd)
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  have hrange : ∀ s : Real, rho s ∈ V := by
    intro s
    apply hbuffer
    by_cases hs0 : rho s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (rho s) 0 margin
        (Set.Icc (0 : Real) b) ⟨le_rfl, hb0.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      have hlo := (hrho_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsb : rho s ≤ b
      · refine Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
          (Set.Icc (0 : Real) b) ⟨(not_le.mp hs0).le, hsb⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (rho s) b margin
          (Set.Icc (0 : Real) b) ⟨hb0.le, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb).le)]
        have hhi := (hrho_range s).2
        dsimp only [d, eps] at hhi
        linarith
  refine ⟨rho, a, d, ha0, hbd, hrho, ?_, hrho_deriv,
    fun s ↦ (hrange s).1, fun s ↦ (hrange s).2⟩
  intro s hs
  simpa only [id_eq] using hrho_id s hs

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lReg_germ
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < 0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc a d) ∧
      (∀ s ∈ Set.Icc a d, HasDerivAt rho 1 s) ∧
      ∀ s : Real, rho s ∈ lRegDomain S T x Z := by
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
      hrho_dom, _hrho_univ⟩ :=
    exists_lReg_germ_in S T x Z hb0 hb Set.univ isOpen_univ
      (fun s _hs ↦ Set.mem_univ s)
  exact ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv, hrho_dom⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRay_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z V : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ∃ rho : Real → Real, ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc (0 : Real) b) ∧
      (∀ s ∈ Set.Icc (0 : Real) b, HasDerivAt rho 1 s) ∧
      (∀ s : Real, rho s ∈ lRegDomain S T x Z) ∧
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M)) ∧
      Set.EqOn
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M))
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z s)
            (lRegJacobiField S T x Z V s) : TangentBundle I M))
        (Set.Icc (0 : Real) b) := by
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    exists_lReg_clamp S T x Z hb0 hb
  have hrho_m : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho := by
    exact contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      ((fun s : Real ↦ ((Z : E), rho s)) : Real → E × Real) :=
    contMDiff_const.prodMk hrho_m
  have hsmooth : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (lRegCurve S T x Z (rho s))
          (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    exact (lRegJacobi_smooth S hS T x V).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  refine ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range, hsmooth, ?_⟩
  intro s hs
  change TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
      (lRegCurve S T x Z (rho s))
      (lRegJacobiField S T x Z V (rho s)) =
    TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
      (lRegCurve S T x Z s) (lRegJacobiField S T x Z V s)
  rw [hrho_id hs]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRay_germ_in
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z V : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z)
    (U : Set Real) (hU : IsOpen U)
    (hsegU : Set.Icc (0 : Real) b ⊆ U) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < 0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc a d) ∧
      (∀ s ∈ Set.Icc a d, HasDerivAt rho 1 s) ∧
      (∀ s : Real, rho s ∈ lRegDomain S T x Z) ∧
      (∀ s : Real, rho s ∈ U) ∧
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M)) ∧
      Set.EqOn
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M))
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z s)
            (lRegJacobiField S T x Z V s) : TangentBundle I M))
        (Set.Icc a d) := by
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
      hrho_dom, hrho_U⟩ :=
    exists_lReg_germ_in S T x Z hb0 hb U hU hsegU
  have hrho_m : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho := by
    exact contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      ((fun s : Real ↦ ((Z : E), rho s)) : Real → E × Real) :=
    contMDiff_const.prodMk hrho_m
  have hsmooth : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (lRegCurve S T x Z (rho s))
          (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    exact (lRegJacobi_smooth S hS T x V).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_dom s)
  refine ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
    hrho_dom, hrho_U, hsmooth, ?_⟩
  intro s hs
  change TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
      (lRegCurve S T x Z (rho s))
      (lRegJacobiField S T x Z V (rho s)) =
    TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
      (lRegCurve S T x Z s) (lRegJacobiField S T x Z V s)
  rw [hrho_id hs]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRay_germ
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z V : TangentSpace I x) {b : Real}
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < 0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Set.Icc a d) ∧
      (∀ s ∈ Set.Icc a d, HasDerivAt rho 1 s) ∧
      (∀ s : Real, rho s ∈ lRegDomain S T x Z) ∧
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M)) ∧
      Set.EqOn
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z (rho s))
            (lRegJacobiField S T x Z V (rho s)) : TangentBundle I M))
        (fun s : Real ↦
          (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
            (lRegCurve S T x Z s)
            (lRegJacobiField S T x Z V s) : TangentBundle I M))
        (Set.Icc a d) := by
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
      hrho_dom, _hrho_univ, hsmooth, heq⟩ :=
    exists_lRay_germ_in S hS T x Z V hb0 hb Set.univ isOpen_univ
      (fun s _hs ↦ Set.mem_univ s)
  exact ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
    hrho_dom, hsmooth, heq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
