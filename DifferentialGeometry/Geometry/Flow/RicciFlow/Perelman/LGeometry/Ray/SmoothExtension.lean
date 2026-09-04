import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Smoothness

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
theorem lRegCurve_isLRegCurveOn
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
theorem exists_lRegDomain_smoothClamp
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
  obtain ⟨rho, lo, hi, hlo0, hbhi, hrho, hrho_id, hrho_deriv, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      (lRegDomain_isOpen S T x Z) hb0 hseg
  refine ⟨rho, hrho, ?_, ?_, hrange⟩
  · intro s hs
    exact hrho_id ⟨hlo0.le.trans hs.1, hs.2.trans hbhi.le⟩
  · intro s hs
    exact hrho_deriv s ⟨hlo0.le.trans hs.1, hs.2.trans hbhi.le⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lRegDomain_smoothGerm_in
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
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      hVopen hb0 hsegV
  refine ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
    fun s ↦ (hrange s).1, fun s ↦ (hrange s).2⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lRegDomain_smoothGerm
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
    exists_lRegDomain_smoothGerm_in S T x Z hb0 hb Set.univ isOpen_univ
      (fun s _hs ↦ Set.mem_univ s)
  exact ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv, hrho_dom⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegJacobiField_smoothClamp
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
    exists_lRegDomain_smoothClamp S T x Z hb0 hb
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
theorem exists_lRegJacobiField_smoothGerm_in
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
    exists_lRegDomain_smoothGerm_in S T x Z hb0 hb U hU hsegU
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
theorem exists_lRegJacobiField_smoothGerm
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
    exists_lRegJacobiField_smoothGerm_in S hS T x Z V hb0 hb Set.univ isOpen_univ
      (fun s _hs ↦ Set.mem_univ s)
  exact ⟨rho, a, d, ha0, hbd, hrho, hrho_id, hrho_deriv,
    hrho_dom, hsmooth, heq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
