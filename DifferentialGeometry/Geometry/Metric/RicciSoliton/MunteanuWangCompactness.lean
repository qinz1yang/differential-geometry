import DifferentialGeometry.Geometry.Comparison.Volume.InfiniteVolume
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Metric.RicciSoliton.MunteanuWang

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem normalizedGradientRicciSoliton_compactSpace_of_sectionalNonnegative_ricci_pos
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hsec : ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v) :
    CompactSpace M := by
  by_contra hnoncompact
  let _ : NoncompactSpace M := not_compactSpace_iff.mp hnoncompact
  let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasureOnCompacts mu :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  let n : Real := Module.finrank Real E
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  have hRicLower : Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g 0 := by
    intro x v
    simpa only [zero_mul] using
      ricciTensor_nonneg_of_sectionalNonnegative (I := I) g x (hsec x) v
  have hmu_top : mu Set.univ = ⊤ := by
    exact Riemannian.VolumeComparison.riemannianVolumeMeasure_univ_eq_top_of_complete_noncompact_ricci_nonnegative
      (I := I) g h.1 hRicLower
  obtain ⟨a, ha, hscalar⟩ :=
    normalizedGradientRicciSoliton_scalar_lower_bound_by_min_rank_potential
      (I := I) h hsec hRic
  let c : Real := n / a
  have hc : 0 < c := div_pos hn ha
  let K : Set M := {x : M | f x ≤ c}
  have hpos : ∀ x : M, 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_ricci_pos (I := I) h hRic
  have sublevel_compact (s : Real) (hs : 0 ≤ s) :
      IsCompact {x : M | f x ≤ s} := by
    have heq : {x : M | f x ≤ s} = (f : M → Real) ⁻¹' Set.Icc 0 s := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
      exact (and_iff_right (hpos x).le).symm
    rw [heq]
    exact (normalizedGradientRicciSoliton_potential_isProperMap (I := I) h).isCompact_preimage
      isCompact_Icc
  have hKcompact : IsCompact K := by
    exact sublevel_compact c hc.le
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  let A : Nat → Set M := fun j => {x : M | f x < j}
  have hAmono : Monotone A := by
    intro j k hjk x hx
    change f x < (j : Real) at hx
    change f x < (k : Real)
    exact hx.trans_le (Nat.cast_le.mpr hjk)
  have hAunion : (⋃ j : Nat, A j) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, A, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨j, hj⟩ := exists_nat_gt (f x)
    exact ⟨j, hj⟩
  have hsup : (⨆ j : Nat, mu (A j)) = ⊤ := by
    rw [← hmu_top, ← hAunion]
    exact hAmono.measure_iUnion.symm
  let B : Real := 2 * mu.real K
  have hB : 0 ≤ B := mul_nonneg (by norm_num) measureReal_nonneg
  obtain ⟨j, hj⟩ := (iSup_eq_top.mp hsup) (ENNReal.ofReal B) (by simp)
  let t : Real := max (j : Real) (c + 1)
  let U : Set M := {x : M | f x < t}
  have hct : c < t := by
    exact lt_of_lt_of_le (lt_add_one c) (le_max_right _ _)
  have ht : 0 < t := hc.trans hct
  have hUcompact : IsCompact {x : M | f x ≤ t} :=
    sublevel_compact t ht.le
  have hUfinite : mu U ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (by
      intro x hx
      change f x < t at hx
      exact hx.le)).trans_lt hUcompact.measure_lt_top
  have hAjU : A j ⊆ U := by
    intro x hx
    change f x < (j : Real) at hx
    change f x < t
    exact hx.trans_le (le_max_left _ _)
  have hAjfinite : mu (A j) ≠ ⊤ :=
    measure_ne_top_of_subset hAjU hUfinite
  have hBltAj : B < mu.real (A j) := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hB hAjfinite).mp hj
  have hvolume_large : 2 * mu.real K < mu.real U := by
    exact hBltAj.trans_le (measureReal_mono hAjU hUfinite)
  have hKsubU : K ⊆ U := by
    intro x hx
    change f x ≤ c at hx
    change f x < t
    exact hx.trans_lt hct
  have hUmeas : MeasurableSet U :=
    (isOpen_lt f.contMDiff.continuous continuous_const).measurableSet
  have hscalar_int : IntegrableOn (metricScalarAt (I := I) g) U mu :=
    ((metricScalar_smooth (I := I) (M := M) g).continuous.continuousOn.integrableOn_compact
      hUcompact).mono_set fun x hx => by
        change f x < t at hx
        exact hx.le
  let S : Set M := U \ K
  have hSsubU : S ⊆ U := sdiff_subset
  have hSmeas : MeasurableSet S := hUmeas.diff hKmeas
  have hSfinite : mu S ≠ ⊤ := measure_ne_top_of_subset hSsubU hUfinite
  have hscalar_intS : IntegrableOn (metricScalarAt (I := I) g) S mu :=
    hscalar_int.mono_set hSsubU
  have hscalar_outside (x : M) (hx : x ∈ S) :
      n ≤ metricScalarAt (I := I) g x := by
    have hfc : c < f x := by
      exact lt_of_not_ge hx.2
    have hac : a * c = n := by
      dsimp only [c]
      field_simp [ha.ne']
    have hnaf : n ≤ a * f x := by
      nlinarith
    simpa only [n, min_eq_left hnaf] using hscalar x
  have hlowerS : n * mu.real S ≤
      ∫ x in S, metricScalarAt (I := I) g x ∂mu :=
    setIntegral_ge_of_const_le_real hSmeas hSfinite hscalar_outside hscalar_intS
  have hnonneg : 0 ≤ᵐ[mu.restrict U] metricScalarAt (I := I) g :=
    Filter.Eventually.of_forall fun x =>
      normalizedGradientRicciSoliton_scalar_nonneg (I := I) h x
  have hmonoset :
      (∫ x in S, metricScalarAt (I := I) g x ∂mu) ≤
        ∫ x in U, metricScalarAt (I := I) g x ∂mu :=
    setIntegral_mono_set hscalar_int hnonneg
      (Filter.Eventually.of_forall hSsubU)
  have hdiff : mu.real S = mu.real U - mu.real K := by
    exact measureReal_sdiff hKsubU hKmeas hUfinite
  have hlower : n * (mu.real U - mu.real K) ≤
      ∫ x in U, metricScalarAt (I := I) g x ∂mu := by
    rw [← hdiff]
    exact hlowerS.trans hmonoset
  have hupper :=
    normalizedGradientRicciSoliton_integral_scalar_le_rank_half_mul_volume_on_lt_sublevel
      (I := I) h t hUcompact
  change (∫ x in U, metricScalarAt (I := I) g x ∂mu) ≤
    n / 2 * mu.real U at hupper
  have hgap : 0 < mu.real U - 2 * mu.real K := by
    linarith
  have hpositive := mul_pos hn hgap
  have hstrict : n / 2 * mu.real U < n * (mu.real U - mu.real K) := by
    nlinarith
  linarith

theorem munteanu_wang_compactness
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hsec : ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hRic : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) g x v v) :
    CompactSpace M := by
  obtain ⟨C, hnormalized⟩ :=
    gradientRicciSoliton_exists_normalized
      (I := I) hcomplete hsol hsigma
  let gHat : SmoothRiemannianMetric I M :=
    scaleMetric (I := I) sigma hsigma g
  let fHat : C^∞⟮I, M; Real⟯ :=
    f + ContMDiffMap.const (I := I)
      (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) (C / sigma)
  have hsecHat : ∀ x : M, metricRm04At (I := I) (M := M) gHat x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) := by
    intro x
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) gHat x).mpr
    intro v w
    rw [show gHat = scaleMetric (I := I) sigma hsigma g by rfl,
      Curvature.metricRmStandard_scale]
    exact mul_nonneg hsigma.le
      ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) (M := M) g x).mp (hsec x) v w)
  have hRicHat : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < ricciTensor (I := I) gHat x v v := by
    intro x v hv
    rw [show gHat = scaleMetric (I := I) sigma hsigma g by rfl,
      Curvature.ricciTensor_scaleMetric]
    exact hRic x v hv
  exact normalizedGradientRicciSoliton_compactSpace_of_sectionalNonnegative_ricci_pos
    (I := I) (g := gHat) (f := fHat) hnormalized hsecHat hRicHat

theorem positive_sectional_gradientRicciSoliton_compactness
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hdim : 2 ≤ Module.finrank Real E)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StandardAt (I := I) (M := M) g x v w w v) :
    CompactSpace M := by
  apply munteanu_wang_compactness (I := I) hcomplete hsol hsigma
  · intro x
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mpr
    intro v w
    by_cases hli : LinearIndependent Real (vec2 (I := I) v w)
    · exact (hsec x v w hli).le
    · by_cases hw : w = 0
      · subst w
        change 0 ≤ metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) v 0 0 v)
        have hzero := (metricRm04At (I := I) (M := M) g x).map_update_zero
          (vec4 (I := I) v 0 0 v) (1 : Fin 4)
        have hupdate : Function.update (vec4 (I := I) v 0 0 v)
            (1 : Fin 4) 0 = vec4 (I := I) v 0 0 v := by
          funext a
          fin_cases a <;> simp [vec4, Function.update]
        rw [hupdate] at hzero
        exact hzero.ge
      · have hdep : ∃ r : Real, r • w = v := by
          rw [linearIndependent_fin2] at hli
          have hli' : ¬ (w ≠ 0 ∧ ∀ r : Real, r • w ≠ v) := by
            simpa [vec2] using hli
          obtain ⟨r, hr⟩ := Classical.not_forall.mp (fun h => hli' ⟨hw, h⟩)
          exact ⟨r, not_ne_iff.mp hr⟩
        obtain ⟨r, hr⟩ := hdep
        have hskew :=
          (mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp
            (metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (M := M) g x)).1 w w w w
        have hzero : metricRm04StandardAt (I := I) (M := M) g x w w w w = 0 := by
          change metricRm04StandardAt (I := I) (M := M) g x w w w w =
            -metricRm04StandardAt (I := I) (M := M) g x w w w w at hskew
          linarith
        rw [← hr]
        change 0 ≤ metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) (r • w) w w (r • w))
        have hsmul0 := (metricRm04At (I := I) (M := M) g x).map_update_smul
          (vec4 (I := I) w w w w) (0 : Fin 4) r w
        have hupdate0 (z : TangentSpace I x) :
            Function.update (vec4 (I := I) w w w w) (0 : Fin 4) z =
              vec4 (I := I) z w w w := by
          funext a
          fin_cases a <;> simp [vec4, Function.update]
        rw [hupdate0, hupdate0] at hsmul0
        have hsmul3 := (metricRm04At (I := I) (M := M) g x).map_update_smul
          (vec4 (I := I) (r • w) w w w) (3 : Fin 4) r w
        have hupdate3 (z : TangentSpace I x) :
            Function.update (vec4 (I := I) (r • w) w w w) (3 : Fin 4) z =
              vec4 (I := I) (r • w) w w z := by
          funext a
          fin_cases a <;> simp [vec4, Function.update]
        rw [hupdate3, hupdate3] at hsmul3
        rw [hsmul3, hsmul0]
        have hzero' : metricRm04At (I := I) (M := M) g x
            (vec4 (I := I) w w w w) = 0 := by
          simpa only [metricRm04StandardAt_apply] using hzero
        simp only [hzero', smul_zero, le_refl]
  · intro x v hv
    apply Riemannian.BonnetMyers.ricci_pos_of_sec
      (I := I) g x (by omega) (fun a b ha hb hab => ?_) hv
    apply hsec x a b
    rw [linearIndependent_fin2]
    simp only [vec2]
    refine ⟨hb, ?_⟩
    intro r hr
    have hinner : r * g.inner x b b = 0 := by
      calc
        r * g.inner x b b = g.inner x (r • b) b := by
          rw [(g.inner x).map_smul, smul_apply, smul_eq_mul]
        _ = g.inner x a b := congrArg (fun z => g.inner x z b) hr
        _ = 0 := hab
    have hbb : 0 < g.inner x b b := g.pos x b hb
    have hrzero : r = 0 := by
      nlinarith
    rw [hrzero, zero_smul] at hr
    exact ha hr.symm

end DifferentialGeometry.Geometry
