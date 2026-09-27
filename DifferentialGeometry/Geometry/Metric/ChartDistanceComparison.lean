import DifferentialGeometry.Geometry.Metric.LocalChartDistance

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set MeasureTheory DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_symm_chart_le_of_segment
    (g : SmoothRiemannianMetric I M) (p : M) {x y : E} {K : ℝ} (hK : 0 ≤ K)
    (hsegment : segment ℝ x y ⊆ (extChartAt I p).target)
    (hbound : ∀ z ∈ segment ℝ x y, ∀ v : TangentSpace I p,
      let e := trivializationAt E (TangentSpace I) p
      let q := (extChartAt I p).symm z
      Real.sqrt (g.inner q
        (e.symmL ℝ q (e.continuousLinearMapAt ℝ p v))
        (e.symmL ℝ q (e.continuousLinearMapAt ℝ p v))) ≤
          K * Real.sqrt (g.inner p v v)) :
    let e := trivializationAt E (TangentSpace I) p
    let w := e.symmL ℝ p (y - x)
    riemannianEDistOf g ((extChartAt I p).symm x) ((extChartAt I p).symm y) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt (g.inner p w w)) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let e := trivializationAt E (TangentSpace I) p
  let w := e.symmL ℝ p (y - x)
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  let γ := (extChartAt I p).symm ∘ η
  have hηseg : MapsTo η (Icc 0 1) (segment ℝ x y) := by
    change Icc 0 1 ⊆ η ⁻¹' segment ℝ x y
    rw [← image_subset_iff]
    simpa only [η, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
      using (Subset.rfl : segment ℝ x y ⊆ segment ℝ x y)
  have hη : MapsTo η (Icc 0 1) (extChartAt I p).target := by
    intro t ht
    exact hsegment (hηseg ht)
  have hηsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc 0 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (ContinuousAffineMap.contDiff _).contDiffOn
  have hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm p).comp hηsmooth hη
  have hd : riemannianEDistOf g ((extChartAt I p).symm x) ((extChartAt I p).symm y) ≤
      pathELength I γ 0 1 :=
    riemannianEDist_le_pathELength hγ
      (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq])
      (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
  apply hd.trans
  change pathELength I γ 0 1 ≤
    ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt (g.inner p w w))
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1,
        ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt (g.inner p w w)) := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hγchart : γ t ∈ (chartAt H p).source := by
        simpa only [γ, Function.comp_apply, extChartAt_source] using
          (extChartAt I p).map_target (hη ht)
      have hcoord : extChartAt I p (γ t) = η t :=
        (extChartAt I p).right_inv (hη ht)
      have hder : mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t =
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (η t)).comp
            (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t) := by
        apply mfderivWithin_comp
        · exact mdifferentiableWithinAt_extChartAt_symm (hη ht)
        · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
        · intro s hs
          exact extChartAt_target_subset_range p (hη hs)
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have hηder : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc 0 1) t 1 = y - x := by
        rw [mfderivWithin_eq_fderivWithin,
          fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one t ht)
            (ContinuousAffineMap.differentiableAt _)]
        simp only [η, ContinuousAffineMap.fderiv]
        have hlin := (ContinuousAffineMap.lineMap (R := ℝ) x y).contLinear_map_vsub (1 : ℝ) 0
        simp only [vsub_eq_sub, sub_zero, ContinuousAffineMap.coe_lineMap_eq,
          AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at hlin
        convert hlin using 1; rfl
      have hS : mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (η t) =
          e.symmL ℝ (γ t) := by
        rw [TangentBundle.symmL_trivializationAt hγchart, hcoord]
      rw [hder, ContinuousLinearMap.comp_apply, hηder, hS]
      have hw : e.continuousLinearMapAt ℝ p w = y - x :=
        e.continuousLinearMapAt_symmL (FiberBundle.mem_baseSet_trivializationAt' p) (y - x)
      have hn := hbound (η t) (hηseg ht) w
      dsimp only at hn
      rw [hw] at hn
      have hnorm : ‖e.symmL ℝ (γ t) (y - x)‖ ≤ K * Real.sqrt (g.inner p w w) := by
        rw [norm_eq_sqrt_real_inner]
        convert hn using 1; rfl
      have henorm := ENNReal.ofReal_le_ofReal hnorm
      simp only [ofReal_norm, ENNReal.ofReal_mul hK] at henorm
      convert henorm using 1; rfl
    _ = _ := by simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem frozen_displacement_le_of_intrinsic_ball
    (g : SmoothRiemannianMetric I M) (p : M) (s : Set M)
    {K : ℝ} (hK : 1 < K) (c : ℝ≥0) (hc : 0 < c)
    (hball : {q | riemannianEDistOf g p q < c} ⊆ s)
    (hchart : s ⊆ (chartAt H p).source)
    (hforward : ∀ q ∈ s, ∀ v : TangentSpace I q,
      let e := trivializationAt E (TangentSpace I) p
      Real.sqrt (g.inner p
        (e.symmL ℝ p (e.continuousLinearMapAt ℝ q v))
        (e.symmL ℝ p (e.continuousLinearMapAt ℝ q v))) ≤
          K * Real.sqrt (g.inner q v v))
    (x y : M) (hx : riemannianEDistOf g p x < (c / 3 : ℝ≥0))
    (hsmall :
      let e := trivializationAt E (TangentSpace I) p
      let w := e.symmL ℝ p (extChartAt I p y - extChartAt I p x)
      ENNReal.ofReal (Real.sqrt (g.inner p w w)) < (c / 3 : ℝ≥0)) :
    let e := trivializationAt E (TangentSpace I) p
    let w := e.symmL ℝ p (extChartAt I p y - extChartAt I p x)
    ENNReal.ofReal (Real.sqrt (g.inner p w w)) ≤
      ENNReal.ofReal K * riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let e := trivializationAt E (TangentSpace I) p
  let w := e.symmL ℝ p (extChartAt I p y - extChartAt I p x)
  let N := ENNReal.ofReal (Real.sqrt (g.inner p w w))
  change N < (c / 3 : ℝ≥0) at hsmall
  change N ≤ ENNReal.ofReal K * riemannianEDistOf g x y
  have hK0 : ENNReal.ofReal K ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (zero_lt_one.trans hK)).ne'
  have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hK.le
  by_contra h
  have hd : riemannianEDistOf g x y < N / ENNReal.ofReal K := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl hKtop)).mpr
    simpa only [mul_comm] using lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hd
  have hdiv : N / ENNReal.ofReal K ≤ N := by
    simpa only [div_one] using ENNReal.div_le_div_left hKone N
  have hlength' : pathELength I γ 0 1 < (c / 3 : ℝ≥0) :=
    (hlength.trans_le hdiv).trans hsmall
  have hstart : riemannianEDistOf g p (γ 0) < (c / 3 : ℝ≥0) := by rwa [hγ0]
  have hsum : ((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0) < (c : ℝ≥0∞) := by
    exact_mod_cast (show c / 3 + c / 3 < c by linarith)
  have hmap : MapsTo γ (Icc 0 1) s :=
    mapsTo_of_riemannianEDistOf_add_pathELength_lt g p s c hball γ hγ
      ((ENNReal.add_lt_add hstart hlength').trans hsum)
  have hdisp := chart_displacement_le_pathELength g p (zero_lt_one.trans hK).le γ hγ
    (fun _ ht => hchart (hmap ht)) (fun t ht v => hforward (γ t) (hmap ht) v)
  dsimp only at hdisp
  rw [hγ0, hγ1] at hdisp
  change N ≤ ENNReal.ofReal K * pathELength I γ 0 1 at hdisp
  have hstrict : ENNReal.ofReal K * pathELength I γ 0 1 < N := by
    have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl hKtop)).mp hlength
    simpa only [mul_comm] using hmul
  exact (not_lt_of_ge hdisp) hstrict

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_riemannianEDistOf_comparison [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {K : ℝ} (hK : 1 < K) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧ (U : Set M) ⊆ (chartAt H p).source ∧
      ∀ x ∈ U, ∀ y ∈ U,
        let e := trivializationAt E (TangentSpace I) p
        let w := e.symmL ℝ p (extChartAt I p y - extChartAt I p x)
        let N := ENNReal.ofReal (Real.sqrt (g.inner p w w))
        N ≤ ENNReal.ofReal K * riemannianEDistOf g x y ∧
          riemannianEDistOf g x y ≤ ENNReal.ofReal K * N := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let e := trivializationAt E (TangentSpace I) p
  let S := e.symmL ℝ p
  let φ := extChartAt I p
  have norm_g (q : M) (v : TangentSpace I q) :
      ‖v‖ = Real.sqrt (g.inner q v v) := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hgood := eventually_tangent_transport_le g p hK
  dsimp only at hgood
  obtain ⟨W, hWgood, hWopen, hpW⟩ := mem_nhds_iff.mp hgood
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I (hWopen.mem_nhds hpW)
  have hc3 : 0 < ((c / 3 : ℝ≥0) : ℝ≥0∞) := by positivity
  have hdist : {q | riemannianEDistOf g p q < (c / 3 : ℝ≥0)} ∈ 𝓝 p :=
    eventually_riemannianEDist_lt I p hc3
  let V := W ∩ {q | riemannianEDistOf g p q < (c / 3 : ℝ≥0)}
  have hV : V ∈ 𝓝 p := inter_mem (hWopen.mem_nhds hpW) hdist
  have hpre : φ.symm ⁻¹' V ∈ 𝓝[range I] (φ p) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) p, mem_map] at hV
    exact hV
  let A : Set E := {z | ‖S (z - φ p)‖ < (c : ℝ) / 6}
  have hA : A ∈ 𝓝 (φ p) := by
    have hfn : Continuous (fun z : E => ‖S (z - φ p)‖) :=
      (S.continuous.comp (continuous_id.sub continuous_const)).norm
    have hopen : IsOpen A := isOpen_lt hfn continuous_const
    apply hopen.mem_nhds
    change ‖S (φ p - φ p)‖ < (c : ℝ) / 6
    simp only [sub_self, map_zero, norm_zero]
    positivity
  have hcontrolled : (φ.target ∩ φ.symm ⁻¹' V) ∩ A ∈ 𝓝[range I] (φ p) :=
    inter_mem (inter_mem (extChartAt_target_mem_nhdsWithin p) hpre)
      (mem_nhdsWithin_of_mem_nhds hA)
  obtain ⟨r, hr, hC⟩ := Metric.mem_nhdsWithin_iff.mp hcontrolled
  let C := Metric.ball (φ p) r ∩ range I
  have hCnhds : φ ⁻¹' C ∈ 𝓝 p := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (mem_extChartAt_source p)
    change Metric.ball (φ p) r ∩ range I ∈ 𝓝[range I] (φ p)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hr)
  obtain ⟨U, hU, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem hCnhds (chart_source_mem_nhds H p))
  refine ⟨⟨U, hUopen⟩, hpU, fun x hx => (hU hx).2, ?_⟩
  intro x hx y hy
  have hxC : φ x ∈ C := (hU hx).1
  have hyC : φ y ∈ C := (hU hy).1
  have hxchart : x ∈ φ.source := by simpa only [φ, extChartAt_source] using (hU hx).2
  have hychart : y ∈ φ.source := by simpa only [φ, extChartAt_source] using (hU hy).2
  have hseg : segment ℝ (φ x) (φ y) ⊆ C :=
    ((convex_ball _ _).inter I.convex_range).segment_subset hxC hyC
  have hnx : ‖S (φ x - φ p)‖ < (c : ℝ) / 6 := (hC hxC).2
  have hny : ‖S (φ y - φ p)‖ < (c : ℝ) / 6 := (hC hyC).2
  have hnorm : ‖S (φ y - φ x)‖ < (c : ℝ) / 3 := calc
    ‖S (φ y - φ x)‖ = ‖S (φ y - φ p) - S (φ x - φ p)‖ := by
      congr 1
      rw [← map_sub]
      congr 1
      abel
    _ ≤ ‖S (φ y - φ p)‖ + ‖S (φ x - φ p)‖ := norm_sub_le _ _
    _ < (c : ℝ) / 6 + (c : ℝ) / 6 := add_lt_add hny hnx
    _ = (c : ℝ) / 3 := by ring
  have hsmall : ENNReal.ofReal (Real.sqrt (g.inner p (S (φ y - φ x)) (S (φ y - φ x)))) <
      (c / 3 : ℝ≥0) := by
    rw [← norm_g p _]
    have hcast : ENNReal.ofReal ((c : ℝ) / 3) = (c / 3 : ℝ≥0) := by
      simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
        (show ENNReal.ofReal (((c / 3 : ℝ≥0) : ℝ)) = ((c / 3 : ℝ≥0) : ℝ≥0∞) from
          ENNReal.ofReal_coe_nnreal)
    rw [← hcast]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (c : ℝ) / 3)).mpr hnorm
  have hxstart : riemannianEDistOf g p x < (c / 3 : ℝ≥0) := by
    have h := (hC hxC).1.2.2
    change riemannianEDistOf g p (φ.symm (φ x)) < (c / 3 : ℝ≥0) at h
    rwa [φ.left_inv hxchart] at h
  constructor
  · exact frozen_displacement_le_of_intrinsic_ball g p W hK c hc hball
      (fun _ hq => (hWgood hq).1) (fun q hq v => (hWgood hq).2.1 v) x y hxstart hsmall
  · have hupper := riemannianEDistOf_symm_chart_le_of_segment g p
      (x := φ x) (y := φ y) (zero_lt_one.trans hK).le
      (fun _ hz => (hC (hseg hz)).1.1)
      (fun z hz v => (hWgood (hC (hseg hz)).1.2.1).2.2 v)
    simpa only [φ, (extChartAt I p).left_inv hxchart,
      (extChartAt I p).left_inv hychart] using hupper

end DifferentialGeometry.Geometry.Metric
