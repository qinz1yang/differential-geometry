import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFactor
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow

/-!
# Intrinsic distance of the exact splitting factor

The original zero-fibre subtype distance agrees with the distance of the induced metric. Ambient
minimizing geodesics remain in the slice, and their actual regular-zero lifts retain their length.
-/

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Manifold WithLp MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)

theorem inducedMetric_enorm_val
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ (z : {x : M // (e x).fst = 0}) (v : TangentSpace IZ z),
      ‖mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z v‖ₑ = ‖v‖ₑ := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
    ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
  intro z v
  rw [hnorm, ← inducedMetric_inner g hr hnorm e z v v]
  change ENNReal.ofReal (Real.sqrt (inner ℝ v v)) = ‖v‖ₑ
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

theorem ambient_edist_le_induced_riemannianEDist
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ z w : {x : M // (e x).fst = 0}, edist z w ≤ riemannianEDist IZ z w := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
    ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
  intro z w
  rw [riemannianEDist]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  have hi : ContMDiff IZ I 1 (Subtype.val : {x : M // (e x).fst = 0} → M) :=
    (contMDiff_splittingFactor_val g hr hnorm e).of_le (by
      simpa only [← WithTop.coe_ofNat, ← WithTop.coe_one, ← WithTop.coe_add,
        WithTop.coe_le_coe] using
        (show (1 : ℕ∞) ≤ r + 2 from le_add_of_le_right (by norm_num)))
  let η : Path z.val w.val :=
    ⟨⟨fun t => (γ t).val, continuous_subtype_val.comp γ.continuous⟩,
      congrArg Subtype.val γ.source, congrArg Subtype.val γ.target⟩
  have hη : ContMDiff (𝓡∂ 1) I 1 η := hi.comp hγ
  have hd : edist z.val w.val ≤ ∫⁻ t, ‖mfderiv (𝓡∂ 1) I η t 1‖ₑ := by
    rw [IsRiemannianManifold.out (I := I), riemannianEDist]
    exact (iInf_le _ η).trans (iInf_le _ hη)
  change edist z.val w.val ≤ _
  refine hd.trans_eq (lintegral_congr fun t => ?_)
  have hc := mfderiv_comp t ((hi (γ t)).mdifferentiableAt one_ne_zero)
    ((hγ t).mdifferentiableAt one_ne_zero)
  change mfderiv (𝓡∂ 1) I (Subtype.val ∘ γ) t = _ at hc
  change ‖mfderiv (𝓡∂ 1) I (Subtype.val ∘ γ) t 1‖ₑ = _
  rw [hc, ContinuousLinearMap.comp_apply]
  exact inducedMetric_enorm_val g hr hnorm e (γ t) _

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem exists_unit_segment_in_splittingFactor
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (z w : {x : M // (e x).fst = 0}) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (r : ℕ∞ω) γ ∧
      γ 0 = z.val ∧ γ (dist z w) = w.val ∧
      (∀ s ∈ Icc 0 (dist z w), (e (γ s)).fst = 0) ∧
      ∀ s, ‖mfderiv 𝓘(ℝ, ℝ) I γ s 1‖ₑ = 1 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨u, hu, hseg, hend⟩ := g.exists_unit_segment_expMap hr hnorm z.val w.val
  let γ : ℝ → M := fun s => g.expMap (⟨z.val, s • u⟩ : TangentBundle I M)
  have hD := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ (p : TangentBundle I M) (s : ℝ), (p, s) ∈ g.geodesicFlowDomain :=
    fun p s => by rw [hD]; exact mem_univ _
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I (r : ℕ∞ω) γ := by
    have hl : ContDiff ℝ (r : ℕ∞ω) (fun s : ℝ => s • u) := contDiff_id.smul_const u
    have h := (g.contMDiffOn_expMap_fiber hr1 z.val).comp
      hl.contMDiff.contMDiffOn (s := univ) (fun s _hs => ?_)
    · exact contMDiffOn_univ.mp h
    · exact hmem _ 1
  have hzero : γ 0 = z.val := by
    change g.expMap (⟨z.val, (0 : ℝ) • u⟩ : TangentBundle I M) = z.val
    rw [zero_smul]
    exact g.expMap_zero hr1 z.val
  have hez : e z.val = toLp 2 (0, (e z.val).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext z.property rfl
  have hew : e w.val = toLp 2 (0, (e w.val).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext w.property rfl
  refine ⟨γ, hγ, hzero, hend, ?_, ?_⟩
  · intro s hs
    have hleft : dist z.val (γ s) = s := by
      have h := hseg 0 ⟨le_rfl, dist_nonneg⟩ s hs
      change dist (γ 0) (γ s) = _ at h
      simpa only [hzero, zero_sub, abs_neg, abs_of_nonneg hs.1] using h
    have hright : dist (γ s) w.val = dist z w - s := by
      have h := hseg s hs (dist z.val w.val) ⟨dist_nonneg, le_rfl⟩
      rw [hend, abs_sub_comm] at h
      have hh : s ≤ dist z.val w.val := hs.2
      rw [abs_of_nonneg (sub_nonneg.mpr hh)] at h
      exact h
    apply WithLp.fst_eq_of_dist_add_eq 0 (e z.val).snd (e w.val).snd
    calc
      dist (toLp 2 (0, (e z.val).snd)) (e (γ s)) +
          dist (e (γ s)) (toLp 2 (0, (e w.val).snd)) = dist z w := by
        rw [← hez, ← hew, e.dist_eq, e.dist_eq, hleft, hright]
        ring
      _ = dist (e z.val).snd (e w.val).snd := by
        have h := (WithLp.isometry_prodMk_left (0 : F)).dist_eq (e z.val).snd (e w.val).snd
        rw [← hez, ← hew, e.dist_eq] at h
        exact h
  · intro s
    have heq : γ = fun s => (g.geodesicFlow (⟨z.val, u⟩ : TangentBundle I M) s).proj :=
      funext fun s => g.expMap_smul_eq_proj_geodesicFlow hr1 z.val u s (hmem _ s)
    have hd : mfderiv 𝓘(ℝ, ℝ) I γ s 1 =
        (g.geodesicFlow (⟨z.val, u⟩ : TangentBundle I M) s).snd := by
      rw [heq, (g.hasMFDerivAt_geodesicFlow_proj hr1 (hmem _ s)).mfderiv]
      change @Eq E ((1 : ℝ) •
        ((g.geodesicFlow (⟨z.val, u⟩ : TangentBundle I M) s).snd : E)) _
      exact one_smul ℝ _
    rw [hnorm, hd]
    have hinner := g.inner_geodesicFlow_eq hr1 (⟨z.val, u⟩ : TangentBundle I M) s (hmem _ s)
    have hpoint := congrFun heq s
    change γ s = _ at hpoint
    rw [hpoint, hinner, hu, Real.sqrt_one, ENNReal.ofReal_one]

theorem induced_riemannianEDist_le_ambient_edist
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ z w : {x : M // (e x).fst = 0}, riemannianEDist IZ z w ≤ edist z w := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
    ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  have horder : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 := by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_one, ← WithTop.coe_add,
      WithTop.coe_le_coe] using
      (show (1 : ℕ∞) ≤ r + 2 from le_add_of_le_right (by norm_num))
  have hi := (contMDiff_splittingFactor_val g hr hnorm e).of_le horder
  intro z w
  obtain ⟨γ, hγ, hstart, hend, hzero, hunit⟩ :=
    exists_unit_segment_in_splittingFactor g hr hnorm e z w
  let L : ℝ := dist z w
  have hL : 0 ≤ L := dist_nonneg
  let clipped : ℝ → M := fun s => γ (projIcc 0 L hL s)
  have hclipzero : ∀ s, (e (clipped s)).fst = 0 :=
    fun s => hzero _ (projIcc 0 L hL s).property
  let α : ℝ → {x : M // (e x).fst = 0} := fun s => ⟨clipped s, hclipzero s⟩
  have hclip : ContMDiffOn 𝓘(ℝ, ℝ) I 1 clipped (Icc 0 L) := by
    apply (hγ.of_le (by exact_mod_cast (one_le_two.trans hr))).contMDiffOn.congr
    intro s hs
    simp only [clipped, projIcc_of_mem _ hs]
  have hα : ContMDiffOn 𝓘(ℝ, ℝ) IZ 1 α (Icc 0 L) := by
    intro s hs
    exact DifferentialGeometry.Manifold.RegularZero.contMDiffWithinAt_manifold_lift_of_le
      horder (by simp) (fun x => (e x).fst) (splitting_regularZero_input g hr hnorm e).1
      (splitting_regularZero_input g hr hnorm e).2 clipped (hclip s hs) hclipzero
  have hα0 : α 0 = z := by
    apply Subtype.ext
    simpa only [α, clipped, projIcc_left] using hstart
  have hαL : α L = w := by
    apply Subtype.ext
    simpa only [α, clipped, projIcc_right] using hend
  have hlength : pathELength IZ α 0 L = ENNReal.ofReal L := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo]
    have hu : ∀ s ∈ Ioo 0 L, ‖mfderiv 𝓘(ℝ, ℝ) IZ α s 1‖ₑ = 1 := by
      intro s hs
      have hd := (hα s ⟨hs.1.le, hs.2.le⟩).contMDiffAt (Icc_mem_nhds hs.1 hs.2)
      have hc := mfderiv_comp s ((hi (α s)).mdifferentiableAt one_ne_zero)
        (hd.mdifferentiableAt one_ne_zero)
      have heq : clipped =ᶠ[𝓝 s] γ := by
        filter_upwards [Ioo_mem_nhds hs.1 hs.2] with v hv
        simp only [clipped, projIcc_of_mem _ ⟨hv.1.le, hv.2.le⟩]
      calc
        ‖mfderiv 𝓘(ℝ, ℝ) IZ α s 1‖ₑ =
            ‖mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (α s)
              (mfderiv 𝓘(ℝ, ℝ) IZ α s 1)‖ₑ :=
          (inducedMetric_enorm_val g hr hnorm e (α s) _).symm
        _ = ‖mfderiv 𝓘(ℝ, ℝ) I clipped s 1‖ₑ := by
          rw [← ContinuousLinearMap.comp_apply, ← hc]
          rfl
        _ = 1 := by
          rw [hnorm]
          have hdf := DFunLike.congr_fun (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)) (1 : ℝ)
          change @Eq E (mfderiv 𝓘(ℝ, ℝ) I clipped s 1)
            (mfderiv 𝓘(ℝ, ℝ) I γ s 1) at hdf
          have hp : clipped s = γ s := heq.self_of_nhds
          erw [hdf, hp]
          rw [← hnorm]
          exact hunit s
    rw [setLIntegral_congr_fun measurableSet_Ioo hu]
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  have h := (riemannianEDist_le_pathELength hα hα0 hαL hL).trans_eq hlength
  simpa only [edist_dist] using h

theorem isRiemannianManifold_inducedMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
    IsRiemannianManifold IZ {x : M // (e x).fst = 0} := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
    ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
  exact ⟨fun z w => le_antisymm
    (ambient_edist_le_induced_riemannianEDist g hr hnorm e z w)
    (induced_riemannianEDist_le_ambient_edist g hr hnorm e z w)⟩

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem real_splittingFactor_geometry [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (ℝ × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle
        (TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) :
          {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
    CompleteSpace {x : M // (e x).fst = 0} ∧
      ConnectedSpace {x : M // (e x).fst = 0} ∧
      IsRiemannianManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
        {x : M // (e x).fst = 0} :=
  ⟨completeSpace_splittingFactor e, connectedSpace_splittingFactor e,
    isRiemannianManifold_inducedMetric g hr hnorm e⟩

end DifferentialGeometry.Geometry.ExactSplitting
