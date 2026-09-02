import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceFlux
import DifferentialGeometry.Geometry.Operator.HessianExtrema
import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Morse.Riemannian

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma strictMonoOn_mul_exp_neg_Iic_one :
    StrictMonoOn (fun x : Real => x * Real.exp (-x)) (Set.Iic 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 1) (by fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  change x < 1 at hx
  have hexp : HasDerivAt (fun y : Real => Real.exp (-y))
      (-Real.exp (-x)) x := by
    simpa using! (hasDerivAt_neg x).exp
  have hderiv : HasDerivAt (fun y : Real => y * Real.exp (-y))
      ((1 - x) * Real.exp (-x)) x := by
    simpa [sub_mul] using! (hasDerivAt_id x).mul hexp
  rw [hderiv.deriv]
  exact mul_pos (sub_pos.mpr hx) (Real.exp_pos _)

private lemma strictAntiOn_mul_exp_neg_Ici_one :
    StrictAntiOn (fun x : Real => x * Real.exp (-x)) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) (by fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  change 1 < x at hx
  have hexp : HasDerivAt (fun y : Real => Real.exp (-y))
      (-Real.exp (-x)) x := by
    simpa using! (hasDerivAt_neg x).exp
  have hderiv : HasDerivAt (fun y : Real => y * Real.exp (-y))
      ((1 - x) * Real.exp (-x)) x := by
    simpa [sub_mul] using! (hasDerivAt_id x).mul hexp
  rw [hderiv.deriv]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hx) (Real.exp_pos _)

theorem normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    metricScalarAt (I := I) (M := M) g x ≠ 1 := by
  intro hscalarx
  apply hnonconstant
  have hgradx : gradFun (I := I) g f x = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hcrit
  have hf :=
    normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
      (I := I) h hdim x hscalarx hgradx
  intro y z
  rw [hf y, hf z]

theorem normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt I f x := by
  apply isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (c := (1 - metricScalarAt (I := I) (M := M) g x) / 2) g f x hcrit
  · exact div_ne_zero
      (sub_ne_zero.mpr
        (normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
          (I := I) h hdim hnonconstant x hcrit).symm)
      (by norm_num)
  · intro v w
    exact normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
      (I := I) h hdim x v w

theorem normalizedGradientRicciSoliton_finite_criticalPoints_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    (criticalPoints I f).Finite :=
  finite_criticalPoints_of_compact_of_isNondegenerate f f.contMDiff fun p hp =>
    normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
      h hdim hnonconstant p hp

private theorem exists_local_regularized_gradient_flux_limit
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (p : M)
    (hcrit : IsCriticalPointAt I f p) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ b : M → Real,
      Continuous b → tsupport b ⊆ U →
        Tendsto
          (fun ε : Real => ∫ x,
            ε * (1 - metricScalarAt (I := I) (M := M) g x) * b x *
              (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
                ∂riemannianVolumeMeasure (I := I) (M := M) g)
          (𝓝[>] 0)
          (𝓝 (4 * Real.pi /
            (1 - metricScalarAt (I := I) (M := M) g p) * b p)) := by
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  have hRne : R p ≠ 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant p hcrit
  have hc : (1 - R p) / 2 ≠ 0 := by
    intro hzero
    apply hRne
    linarith
  obtain ⟨U, hU, hlim⟩ :=
    exists_nhds_tendsto_integral_regularized_normGradSqFun_inv_sq_mul_of_hessFun_eq_smul_metric_of_finrank_eq_two
      (I := I) hdim g f p hcrit hc
        (normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
          (I := I) h hdim p)
  refine ⟨U, hU, ?_⟩
  intro b hb hbU
  let B : M → Real := fun x => (1 - R x) * b x
  have hB : Continuous B :=
    (continuous_const.sub (metricScalar_smooth (I := I) (M := M) g).continuous).mul hb
  have hBSupport : tsupport B ⊆ U :=
    tsupport_mul_subset_right.trans hbU
  have ht := hlim B hB hBSupport
  have hlimit :
      Real.pi / ((1 - R p) / 2) ^ 2 * B p =
        4 * Real.pi / (1 - R p) * b p := by
    dsimp only [B]
    field_simp [sub_ne_zero.mpr hRne.symm]
    ring
  rw [hlimit] at ht
  simpa only [B, R, mul_assoc] using ht

omit [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ConnectedSpace M] in
private theorem exists_finite_bumps
    {s : Set M} (hs : s.Finite)
    (U : ↥hs.toFinset → Set M)
    (hU : ∀ p : ↥hs.toFinset, U p ∈ 𝓝 (p : M)) :
    ∃ χ : ∀ p : ↥hs.toFinset, SmoothBumpFunction I (p : M),
      (∀ p, tsupport (χ p : M → Real) ⊆ U p) ∧
      ∀ q ∈ s,
        (fun x : M => 1 - ∑ p : ↥hs.toFinset, (χ p : M → Real) x) =ᶠ[𝓝 q] 0 := by
  classical
  have hnhds : ∀ p : ↥hs.toFinset,
      U p ∩ (s \ {(p : M)})ᶜ ∈ 𝓝 (p : M) := by
    intro p
    apply inter_mem (hU p)
    apply hs.sdiff.isClosed.isOpen_compl.mem_nhds
    exact fun hp => hp.2 rfl
  have hbump : ∀ p : ↥hs.toFinset,
      ∃ χ : SmoothBumpFunction I (p : M),
        tsupport (χ : M → Real) ⊆ U p ∩ (s \ {(p : M)})ᶜ := by
    intro p
    obtain ⟨χ, _, hχ⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) (p : M)).mem_iff.mp
        (hnhds p)
    exact ⟨χ, hχ⟩
  choose χ hχ using hbump
  refine ⟨χ, fun p => (hχ p).trans inter_subset_left, ?_⟩
  intro q hq
  let q' : ↥hs.toFinset := ⟨q, hs.mem_toFinset.mpr hq⟩
  have hnear : ∀ p : ↥hs.toFinset,
      ∀ᶠ x in 𝓝 q, (χ p : M → Real) x = if p = q' then 1 else 0 := by
    intro p
    by_cases hp : p = q'
    · subst p
      filter_upwards [(χ q').eventuallyEq_one] with x hx
      simpa only [if_pos, Pi.one_apply] using hx
    · have hqNotSupport : q ∉ tsupport (χ p : M → Real) := by
        intro hqSupport
        have hqAvoid := (hχ p hqSupport).2
        apply hqAvoid
        refine ⟨hq, ?_⟩
        intro hqp
        apply hp
        apply Subtype.ext
        simpa only [q'] using hqp.symm
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hqNotSupport] with x hx
      simpa only [hp, if_false, Pi.zero_apply] using hx
  have hall : ∀ᶠ x in 𝓝 q, ∀ p ∈ (Finset.univ : Finset ↥hs.toFinset),
      (χ p : M → Real) x = if p = q' then 1 else 0 :=
    (eventually_all_finset (Finset.univ : Finset ↥hs.toFinset)).2
      (fun p _ => hnear p)
  filter_upwards [hall] with x hx
  have hsum : (∑ p : ↥hs.toFinset, (χ p : M → Real) x) =
      ∑ p : ↥hs.toFinset, if p = q' then 1 else 0 :=
    Finset.sum_congr rfl fun p hp => hx p hp
  rw [hsum]
  simp

private theorem sum_regularized_gradient_flux_at_criticalPoints_eq_zero
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    (hfinite : (criticalPoints I f).Finite) :
    (∑ p : ↥hfinite.toFinset,
      4 * Real.pi /
        (1 - metricScalarAt (I := I) (M := M) g (p : M))) = 0 := by
  classical
  let C := hfinite.toFinset
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hlocal : ∀ p : ↥C, ∃ U : Set M, U ∈ 𝓝 (p : M) ∧
      ∀ b : M → Real, Continuous b → tsupport b ⊆ U →
        Tendsto
          (fun ε : Real => ∫ x,
            ε * (1 - R x) * b x *
              (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ)
          (𝓝[>] 0) (𝓝 (4 * Real.pi / (1 - R p) * b p)) := by
    intro p
    have hpcrit : (p : M) ∈ criticalPoints I f := by
      exact hfinite.mem_toFinset.mp p.property
    simpa only [R, μ] using
      exists_local_regularized_gradient_flux_limit
        (I := I) h hdim hnonconstant (p : M) hpcrit
  choose U hU hlimit using hlocal
  obtain ⟨χ, hχSupport, hχNear⟩ :=
    exists_finite_bumps (I := I) hfinite U hU
  let φ : M → Real := fun x => ∑ p : ↥C, (χ p : M → Real) x
  let B : M → Real := fun x => (1 - R x) * (1 - φ x)
  let s : Set M := tsupport B
  let localIntegral : ↥C → Real → Real := fun p ε => ∫ x,
    ε * (1 - R x) * (χ p : M → Real) x *
      (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ
  let remainderIntegral : Real → Real := fun ε => ∫ x in s,
    (ε * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) • B x ∂μ
  have hφContinuous : Continuous φ := by
    exact continuous_finsetSum Finset.univ fun p _ => (χ p).continuous
  have hBContinuous : Continuous B := by
    exact (continuous_const.sub
      (metricScalar_smooth (I := I) (M := M) g).continuous).mul
        (continuous_const.sub hφContinuous)
  have hsCompact : IsCompact s := by
    exact (isClosed_tsupport B).isCompact
  have hsDisjoint : Disjoint s (criticalPoints I f) := by
    rw [Set.disjoint_left]
    intro x hxs hxcrit
    have hnear : ∀ᶠ y in 𝓝 x, B y = 0 := by
      filter_upwards [hχNear x hxcrit] with y hy
      change 1 - ∑ p, (χ p : M → Real) y = 0 at hy
      change (1 - R y) * (1 - ∑ p, (χ p : M → Real) y) = 0
      rw [hy, mul_zero]
    have hxNotSupport : x ∉ tsupport B :=
      notMem_tsupport_iff_eventuallyEq.mpr (by
        filter_upwards [hnear] with y hy
        simpa only [Pi.zero_apply] using hy)
    exact hxNotSupport hxs
  have hBIntegrable : Integrable B μ := by
    exact DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hBContinuous (HasCompactSupport.of_compactSpace B)
  have hremTendsto : Tendsto remainderIntegral (𝓝[>] 0) (𝓝 0) := by
    simpa only [remainderIntegral, μ] using
      tendsto_setIntegral_regularized_normGradSqFun_inv_sq_smul_of_compact_of_disjoint_criticalPoints
        (I := I) hsCompact g f hsDisjoint hBIntegrable.integrableOn
  have hlocalTendsto : ∀ p : ↥C,
      Tendsto (localIntegral p) (𝓝[>] 0)
        (𝓝 (4 * Real.pi / (1 - R p))) := by
    intro p
    simpa only [localIntegral, SmoothBumpFunction.eq_one, mul_one] using
      hlimit p (χ p : M → Real) (χ p).continuous (hχSupport p)
  have hsumTendsto : Tendsto
      (fun ε => ∑ p : ↥C, localIntegral p ε) (𝓝[>] 0)
      (𝓝 (∑ p : ↥C, 4 * Real.pi / (1 - R p))) :=
    tendsto_finsetSum Finset.univ fun p _ => hlocalTendsto p
  have hsumEqNegRemainder : ∀ᶠ ε in 𝓝[>] (0 : Real),
      (∑ p : ↥C, localIntegral p ε) = -remainderIntegral ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have hdenNe : ∀ x : M,
        normGradSqFun (I := I) g f x + ε ≠ 0 := by
      intro x
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (normGradSqFun_nonneg (I := I) g f x) hε)
    have hdenContinuous : Continuous
        (fun x : M => (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) :=
      ((normGradSqFun_continuous (I := I) g f.contMDiff).add
        continuous_const).inv₀ hdenNe |>.pow 2
    let A : ↥C → M → Real := fun p x =>
      ε * (1 - R x) * (χ p : M → Real) x *
        (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
    let D : M → Real := fun x =>
      (ε * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) • B x
    have hAIntegrable : ∀ p ∈ (Finset.univ : Finset ↥C), Integrable (A p) μ := by
      intro p _
      apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g
      · exact (((continuous_const.mul
          (continuous_const.sub
            (metricScalar_smooth (I := I) (M := M) g).continuous)).mul
              (χ p).continuous).mul hdenContinuous)
      · exact HasCompactSupport.of_compactSpace (A p)
    have hASumIntegrable : Integrable (fun x => ∑ p : ↥C, A p x) μ :=
      integrable_finsetSum Finset.univ hAIntegrable
    have hDContinuous : Continuous D := by
      exact (continuous_const.mul hdenContinuous).smul hBContinuous
    have hDIntegrable : Integrable D μ := by
      exact DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g hDContinuous (HasCompactSupport.of_compactSpace D)
    have hdecomp :
        (∑ p : ↥C, localIntegral p ε) + ∫ x, D x ∂μ =
          ∫ x, ε * (1 - R x) *
            (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 ∂μ := by
      change (∑ p ∈ (Finset.univ : Finset ↥C), ∫ x, A p x ∂μ) +
          ∫ x, D x ∂μ = _
      rw [← MeasureTheory.integral_finsetSum Finset.univ hAIntegrable,
        ← integral_add hASumIntegrable hDIntegrable]
      apply integral_congr_ae
      filter_upwards with x
      calc
        (∑ p : ↥C, A p x) + D x =
            ε * (1 - R x) * (∑ p : ↥C, (χ p : M → Real) x) *
                (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 + D x := by
          congr 1
          simp only [A]
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.mul_sum]
        _ = ε * (1 - R x) *
            (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 := by
          simp only [D, B, φ, smul_eq_mul]
          ring
    have hglobal :=
      normalizedGradientRicciSoliton_regularized_gradient_integral_eq_zero
        (I := I) h hdim ε hε
    have hdecompZero : (∑ p : ↥C, localIntegral p ε) + ∫ x, D x ∂μ = 0 := by
      rw [hdecomp]
      simpa only [R, μ] using hglobal
    have hremEq : ∫ x, D x ∂μ = remainderIntegral ε := by
      simp only [remainderIntegral]
      rw [← integral_indicator hsCompact.measurableSet]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        have hBx : B x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp only [D, hBx, smul_zero]
    rw [hremEq] at hdecompZero
    exact eq_neg_of_add_eq_zero_left hdecompZero
  have hsumTendstoZero : Tendsto
      (fun ε => ∑ p : ↥C, localIntegral p ε) (𝓝[>] 0) (𝓝 0) := by
    have hneg := hremTendsto.neg
    have heq :
        (fun ε => ∑ p : ↥C, localIntegral p ε) =ᶠ[𝓝[>] 0]
          (fun ε => -remainderIntegral ε) := hsumEqNegRemainder
    simpa only [neg_zero] using hneg.congr' heq.symm
  have hsumZero : (∑ p : ↥C, 4 * Real.pi / (1 - R p)) = 0 :=
    tendsto_nhds_unique hsumTendsto hsumTendstoZero
  simpa only [C, R] using hsumZero

theorem normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmin : IsLocalMin f x) :
    metricScalarAt (I := I) (M := M) g x < 1 := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMin (I := I) g hmin
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonneg_at_spatial_min
    (I := I) g hmin f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : metricScalarAt (I := I) (M := M) g x ≤ 1 := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe

theorem normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmax : IsLocalMax f x) :
    1 < metricScalarAt (I := I) (M := M) g x := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMax (I := I) g hmax
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonpos_at_spatial_max
    (I := I) g hmax f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : 1 ≤ metricScalarAt (I := I) (M := M) g x := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe.symm

theorem normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    ∃ xmin xmax : M,
      IsMinOn f univ xmin ∧ IsMaxOn f univ xmax ∧
      metricScalarAt (I := I) (M := M) g xmin < 1 ∧
      1 < metricScalarAt (I := I) (M := M) g xmax := by
  obtain ⟨xmin, _, hmin⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMinOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  obtain ⟨xmax, _, hmax⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMaxOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  refine ⟨xmin, xmax, hmin, hmax, ?_, ?_⟩
  · exact
      normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmin (hmin.isLocalMin (by simp))
  · exact
      normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmax (hmax.isLocalMax (by simp))

private theorem normalizedGradientRicciSoliton_critical_scalar_eq_extreme_scalar
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    {xmin xmax p : M}
    (hmin : IsMinOn f univ xmin) (hmax : IsMaxOn f univ xmax)
    (hpcrit : IsCriticalPointAt I f p) :
    metricScalarAt (I := I) (M := M) g p =
        metricScalarAt (I := I) (M := M) g xmin ∨
      metricScalarAt (I := I) (M := M) g p =
        metricScalarAt (I := I) (M := M) g xmax := by
  let R : M → Real := fun x => metricScalarAt (I := I) (M := M) g x
  have hgradp : gradFun (I := I) g f p = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hpcrit
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hRmin : R xmin < 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant xmin (hmin.isLocalMin (by simp))
  have hRmax : 1 < R xmax :=
    normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant xmax (hmax.isLocalMax (by simp))
  have hRpne : R p ≠ 1 :=
    normalizedGradientRicciSoliton_metricScalarAt_ne_one_at_criticalPoint_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant p hpcrit
  have hEqMin : R p * Real.exp (-R p) = R xmin * Real.exp (-R xmin) :=
    normalizedGradientRicciSoliton_metricScalarAt_mul_exp_neg_eq_of_finrank_eq_two_of_gradient_eq_zero
      (I := I) h hdim p xmin hgradp hgradMin
  have hEqMax : R p * Real.exp (-R p) = R xmax * Real.exp (-R xmax) :=
    normalizedGradientRicciSoliton_metricScalarAt_mul_exp_neg_eq_of_finrank_eq_two_of_gradient_eq_zero
      (I := I) h hdim p xmax hgradp hgradMax
  rcases lt_or_gt_of_ne hRpne with hRp | hRp
  · left
    apply strictMonoOn_mul_exp_neg_Iic_one.injOn
    · exact le_of_lt hRp
    · exact le_of_lt hRmin
    · exact hEqMin
  · right
    apply strictAntiOn_mul_exp_neg_Ici_one.injOn
    · exact le_of_lt hRp
    · exact le_of_lt hRmax
    · exact hEqMax

theorem normalizedGradientRicciSoliton_isMinOn_or_isMaxOn_at_criticalPoint_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z)
    (p : M) (hpcrit : IsCriticalPointAt I f p) :
    IsMinOn f univ p ∨ IsMaxOn f univ p := by
  obtain ⟨xmin, xmax, hmin, hmax, _, _⟩ :=
    normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
      (I := I) h hdim hnonconstant
  have hscalar :=
    normalizedGradientRicciSoliton_critical_scalar_eq_extreme_scalar
      (I := I) h hdim hnonconstant hmin hmax hpcrit
  have hgradp : gradFun (I := I) g f p = 0 :=
    gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hpcrit
  have hgradMin : gradFun (I := I) g f xmin = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g
      (hmin.isLocalMin (by simp)) ((f.contMDiff xmin).mdifferentiableAt (by simp))
  have hgradMax : gradFun (I := I) g f xmax = 0 :=
    gradientFun_eq_zero_of_isLocalMax (I := I) g
      (hmax.isLocalMax (by simp)) ((f.contMDiff xmax).mdifferentiableAt (by simp))
  have hfp :=
    normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
      (I := I) h p hgradp
  rcases hscalar with hscalar | hscalar
  · left
    have hfmin :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h xmin hgradMin
    have hfpmin : f p = f xmin := hfp.trans (hscalar.trans hfmin.symm)
    intro x hx
    rw [hfpmin]
    exact hmin hx
  · right
    have hfmax :=
      normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
        (I := I) h xmax hgradMax
    have hfpmax : f p = f xmax := hfp.trans (hscalar.trans hfmax.symm)
    intro x hx
    rw [hfpmax]
    exact hmax hx

end DifferentialGeometry.Geometry
