import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.MinimizerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
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
private theorem rayLag_cont
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) :
    ContinuousOn
      (fun q : E × Real ↦
        lRegLag S T (fun s ↦ lRegCurve S T x q.1 s) q.2)
      (lRegJointDom S T x) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let U := lRegJointDom S T x
  let F : E × Real → M := fun q ↦ lRegCurve S T x q.1 q.2
  have hUopen : IsOpen U := lRegJointDom_open S hS T x
  have hF : ContMDiffOn J I ∞ F U := by
    simpa only [J, F, U] using lRegCurve_smoothOn S hS T x
  have htm :=
    hF.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)) :
          TangentBundle J (E × Real))) := by
    have hE : ContMDiff 𝓘(Real, E) 𝓘(Real, E).tangent ∞
        (fun z : E ↦
          (TotalSpace.mk' E z (0 : E) : TangentBundle 𝓘(Real, E) E)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : E ↦ (0 : E))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) :
            TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, E).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, E) E
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    have h := hsymm.comp hpair
    change ContMDiff J J.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)) :
          TangentBundle J (E × Real))) at h
    exact h
  have hvelSmooth : ContMDiffOn J I.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (F q) (lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2) :
            TangentBundle I M)) U := by
    have hcomp : ContMDiffOn J I.tangent ∞
        (fun q : E × Real ↦
          tangentMapWithin J I F U
            (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))) U :=
      htm.comp (hunit.contMDiffOn (s := U)) (fun _ hq ↦ hq)
    refine hcomp.congr ?_
    intro q hq
    have hwithin : mfderivWithin J I F U q = mfderiv J I F q :=
      mfderivWithin_of_isOpen hUopen hq
    have hdiff : MDifferentiableAt J I F q :=
      ((hF q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
    have hsplit := mfderiv_prod_eq_add_apply
      (I := 𝓘(Real, E)) (I' := 𝓘(Real, Real)) (I'' := I)
      (f := F) (p := q) (v := ((0 : E), (1 : Real))) hdiff
    have hzero : mfderiv 𝓘(Real, E) I
        (fun z : E ↦ F (z, q.2)) q.1 (0 : E) = 0 := map_zero _
    rw [hzero, zero_add] at hsplit
    have hjoint : mfderiv J I F q ((0 : E), (1 : Real)) =
        lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2 := by
      simpa only [lVelocity] using hsplit
    change TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (F q) (lVelocity (I := I) (fun s ↦ F (q.1, s)) q.2) =
      tangentMapWithin J I F U
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))
    simp only [tangentMapWithin, hwithin, hjoint]
  let P := {q : E × Real // q ∈ U}
  let timeLift : P → {t : Real // t ∈ D.carrier} := fun q ↦
    ⟨T - q.1.2 ^ 2, D.regular_subset
      (lRegDomain_reg S T x q.1.1 q.2)⟩
  let velLift : P → TangentBundle I M := fun q ↦
    ⟨F q.1, lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2⟩
  have htime : Continuous timeLift :=
    ((continuous_const.sub
      ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _)
  have hvel : Continuous velLift := by
    have hvelOn := hvelSmooth.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at hvelOn
    change Continuous velLift at hvelOn
    exact hvelOn
  have hbase : Continuous (fun q : P ↦ F q.1) := by
    have hbaseOn := hF.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at hbaseOn
    change Continuous (fun q : P ↦ F q.1) at hbaseOn
    exact hbaseOn
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hS.smoothMetric
      (K := D.carrier) (fun _ ht ↦ ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)) := by
    change Continuous (fun q : P ↦
      (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
        (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)) at hkin0
    exact hkin0
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P ↦
      (1 / 2 : Real) *
          (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
            (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
            (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (T - q.1.2 ^ 2) (F q.1)) :=
    continuous_const.mul hkin |>.add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : P ↦
    (1 / 2 : Real) *
        (S.base.metric (T - q.1.2 ^ 2)).inner (F q.1)
          (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2)
          (lVelocity (I := I) (fun s ↦ F (q.1.1, s)) q.1.2) +
      2 * q.1.2 ^ 2 * S.scalar (T - q.1.2 ^ 2) (F q.1))
  exact hlag

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayTail_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {K : Set E} {a b : Real}
    (hK : IsCompact K)
    (hdom : K ×ˢ Icc a b ⊆ lRegJointDom S T x) :
    ∃ C : Real, 0 ≤ C ∧ ∀ Z ∈ K, ∀ c ∈ Icc a b,
      |lRegAction S T (lRegCurve S T x Z) c b| ≤ C * (b - c) := by
  let Q : Set (E × Real) := K ×ˢ Icc a b
  let lag : E × Real → Real := fun q ↦
    lRegLag S T (fun s ↦ lRegCurve S T x q.1 s) q.2
  have hQ : IsCompact Q := hK.prod isCompact_Icc
  have hcont : ContinuousOn lag Q := by
    exact (rayLag_cont (I := I) S hS T x).mono hdom
  obtain ⟨C₀, hC₀⟩ := hQ.exists_bound_of_continuousOn hcont
  let C : Real := max C₀ 0
  refine ⟨C, le_max_right C₀ 0, ?_⟩
  intro Z hZ c hc
  have hcb : c ≤ b := hc.2
  have hsub : Icc c b ⊆ Icc a b := by
    intro s hs
    exact ⟨hc.1.trans hs.1, hs.2⟩
  have hlagBound : ∀ s ∈ Icc c b, |lag (Z, s)| ≤ C := by
    intro s hs
    exact (hC₀ (Z, s) ⟨hZ, hsub hs⟩).trans (le_max_left C₀ 0)
  have hnorm :
      ‖∫ s in c..b, lag (Z, s)‖ ≤ C * |b - c| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hsIcc : s ∈ Icc c b := by
      simpa only [uIcc_of_le hcb] using uIoc_subset_uIcc hs
    simpa only [Real.norm_eq_abs] using hlagBound s hsIcc
  simpa only [lRegAction, lag, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcb)]
    using hnorm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayTail_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : Nat → E) {a b : Real}
    (hZ : Bornology.IsBounded (range Z))
    (hdom : closure (range Z) ×ˢ Icc a b ⊆ lRegJointDom S T x) :
    ∃ C : Real, 0 ≤ C ∧ ∀ n, ∀ c ∈ Icc a b,
      |lRegAction S T (lRegCurve S T x (Z n)) c b| ≤ C * (b - c) := by
  obtain ⟨C, hC, hall⟩ := lRayTail_bound (I := I) S hS T x
    hZ.isCompact_closure hdom
  refine ⟨C, hC, ?_⟩
  intro n c hc
  exact hall (Z n) (subset_closure ⟨n, rfl⟩) c hc

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
