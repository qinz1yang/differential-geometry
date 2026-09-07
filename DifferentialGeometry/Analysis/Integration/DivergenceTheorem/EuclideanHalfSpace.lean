import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.HalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import DifferentialGeometry.Analysis.Calculus.Trace
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Analysis.Calculus.FDeriv.Const

open MeasureTheory Set Filter
open scoped Topology

private local instance euclideanMeasurableSpace (n : Nat) :
    MeasurableSpace (EuclideanSpace Real (Fin (n + 1))) := borel _
private local instance euclideanBorelSpace (n : Nat) :
    BorelSpace (EuclideanSpace Real (Fin (n + 1))) := ⟨rfl⟩

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.Integral.Measure

private noncomputable def euclideanTailHead (n : Nat) :
    EuclideanSpace Real (Fin (n + 1)) ≃L[Real] ((Fin n → Real) × Real) :=
  (EuclideanSpace.equiv (Fin (n + 1)) Real).trans
    ((Fin.consEquivL Real (fun _ : Fin (n + 1) => Real)).symm.trans
      (ContinuousLinearEquiv.prodComm Real Real (Fin n → Real)))

private theorem euclideanTailHead_symm_apply (n : Nat) (p : (Fin n → Real) × Real) :
    (euclideanTailHead n).symm p = WithLp.toLp 2 (Fin.cons p.2 p.1) := rfl


theorem integral_trace_fderivWithin_euclidean_half_space_of_hasCompactSupport
    {n : Nat} {a : Real}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hu : ContDiffOn Real 1 u {x | a ≤ x 0}) (hcs : HasCompactSupport u) :
    ∫ x in {x | a < x 0}, LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
        (fderivWithin Real u {x | a ≤ x 0} x).toLinearMap
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  let e := euclideanTailHead n
  let v : ((Fin n → Real) × Real) → (Fin n → Real) × Real := e ∘ u ∘ e.symm
  have hpre : e.symm ⁻¹' {x | a ≤ x 0} = univ ×ˢ Ici a := by
    ext p
    simp [e, euclideanTailHead_symm_apply]
  have hv : ContDiffOn Real 1 v (univ ×ˢ Ici a) := by
    apply e.contDiff.comp_contDiffOn
    apply hu.comp e.symm.contDiff.contDiffOn
    intro p hp
    rw [← hpre] at hp
    exact hp
  have hvcs : HasCompactSupport v :=
    (hcs.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding).comp_left e.map_zero
  have hflux := integral_trace_fderivWithin_half_space_of_hasCompactSupport
    (mu := (volume : Measure (Fin n → Real))) hv hvcs
  rw [integral_modelHaar_half_space_eq_integral_prod]
  have htrace : ∀ᵐ p ∂((volume : Measure (Fin n → Real)).prod (volume.restrict (Ioi a))),
      LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real u {x | a ≤ x 0} (WithLp.toLp 2 (Fin.cons p.2 p.1))).toLinearMap =
        LinearMap.trace Real ((Fin n → Real) × Real)
          (fderivWithin Real v (univ ×ˢ Ici a) p).toLinearMap := by
    have hmem : ∀ᵐ p ∂((volume : Measure (Fin n → Real)).prod (volume.restrict (Ioi a))),
        p.2 ∈ Ioi a := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
      filter_upwards with z
      exact ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with p hp
    have hps : p ∈ univ ×ˢ Ici a := ⟨mem_univ _, mem_Ici.mpr (mem_Ioi.mp hp).le⟩
    have hdiff : UniqueDiffWithinAt Real (e.symm ⁻¹' {x | a ≤ x 0}) p := by
      rw [hpre]
      exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ici a) p hps
    have h := trace_fderivWithin_conj (u := u) e hdiff
    rw [hpre] at h
    exact h.symm
  rw [integral_congr_ae htrace, hflux, smul_neg]
  rfl

theorem integral_mul_trace_fderivWithin_add_fderivWithin_euclidean_half_space_of_hasCompactSupport
    {n : Nat} {a : Real}
    {phi : EuclideanSpace Real (Fin (n + 1)) → Real}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hphi : ContDiffOn Real 1 phi {x | a ≤ x 0})
    (hu : ContDiffOn Real 1 u {x | a ≤ x 0})
    (hcs : HasCompactSupport (fun x => phi x • u x)) :
    ∫ x in {x | a < x 0}, phi x *
        LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real u {x | a ≤ x 0} x).toLinearMap +
        fderivWithin Real phi {x | a ≤ x 0} x (u x)
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, phi (WithLp.toLp 2 (Fin.cons a z)) *
          u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  have h := integral_trace_fderivWithin_euclidean_half_space_of_hasCompactSupport
    (hphi.smul hu) hcs
  convert h using 1
  · apply integral_congr_ae
    have hopen : IsOpen {x : EuclideanSpace Real (Fin (n + 1)) | a < x 0} :=
      isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    have hxs : x ∈ {x : EuclideanSpace Real (Fin (n + 1)) | a ≤ x 0} := le_of_lt hx
    have hdiff : UniqueDiffWithinAt Real {x : EuclideanSpace Real (Fin (n + 1)) | a ≤ x 0} x :=
      (hopen.uniqueDiffWithinAt hx).mono (fun y h => show a ≤ y 0 from le_of_lt h)
    rw [fderivWithin_smul hdiff (hphi.differentiableOn one_ne_zero x hxs)
      (hu.differentiableOn one_ne_zero x hxs)]
    change _ = LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
      (phi x • (fderivWithin Real u {x | a ≤ x 0} x).toLinearMap +
        (fderivWithin Real phi {x | a ≤ x 0} x).toLinearMap.smulRight (u x))
    rw [map_add, map_smul, LinearMap.trace_smulRight]
    rfl
  · rfl

theorem integral_mul_trace_fderivWithin_add_fderivWithin_withDensity_euclidean_half_space_of_hasCompactSupport
    {n : Nat} {a : Real}
    {phi rho : EuclideanSpace Real (Fin (n + 1)) → Real}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hphi : ContDiffOn Real 1 phi {x | a ≤ x 0})
    (hrho : AEMeasurable rho
      ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0}))
    (hu : ContDiffOn Real 1 (fun x => rho x • u x) {x | a ≤ x 0})
    (hpos : ∀ᵐ x ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
      {x | a < x 0}), 0 < rho x)
    (hcs : HasCompactSupport (fun x => phi x • (rho x • u x))) :
    ∫ x, phi x *
        (LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real (fun y => rho y • u y) {x | a ≤ x 0} x).toLinearMap / rho x) +
        fderivWithin Real phi {x | a ≤ x 0} x (u x)
        ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
          {x | a < x 0}).withDensity (fun x => ENNReal.ofReal (rho x)) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, phi (WithLp.toLp 2 (Fin.cons a z)) *
          rho (WithLp.toLp 2 (Fin.cons a z)) * u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  have h := integral_mul_trace_fderivWithin_add_fderivWithin_euclidean_half_space_of_hasCompactSupport
    hphi hu hcs
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hrho.ennreal_ofReal
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top) _]
  calc
    _ = ∫ x in {x | a < x 0}, phi x *
        LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real (fun y => rho y • u y) {x | a ≤ x 0} x).toLinearMap +
        fderivWithin Real phi {x | a ≤ x 0} x (rho x • u x)
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) := by
      apply integral_congr_ae
      filter_upwards [hpos] with x hx
      rw [ENNReal.toReal_ofReal hx.le, smul_eq_mul, map_smul, smul_eq_mul, mul_add]
      congr 1
      rw [mul_left_comm, mul_div_cancel₀ _ hx.ne']
    _ = _ := by simpa only [PiLp.smul_apply, smul_eq_mul, mul_assoc] using h

theorem integral_trace_fderivWithin_withDensity_euclidean_half_space_of_hasCompactSupport
    {n : Nat} {a : Real}
    {rho : EuclideanSpace Real (Fin (n + 1)) → Real}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hrho : AEMeasurable rho
      ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict {x | a < x 0}))
    (hu : ContDiffOn Real 1 (fun x => rho x • u x) {x | a ≤ x 0})
    (hpos : ∀ᵐ x ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
      {x | a < x 0}), 0 < rho x)
    (hcs : HasCompactSupport (fun x => rho x • u x)) :
    ∫ x, LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
        (fderivWithin Real (fun y => rho y • u y) {x | a ≤ x 0} x).toLinearMap / rho x
        ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
          {x | a < x 0}).withDensity (fun x => ENNReal.ofReal (rho x)) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, rho (WithLp.toLp 2 (Fin.cons a z)) *
          u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  have h := integral_mul_trace_fderivWithin_add_fderivWithin_withDensity_euclidean_half_space_of_hasCompactSupport
    (phi := fun _ => 1) contDiffOn_const hrho hu hpos (by simpa only [one_smul] using hcs)
  simpa using h

theorem integral_trace_fderivWithin_euclidean_half_space_inter_of_hasCompactSupport
    {n : Nat} {a : Real}
    {U : Set (EuclideanSpace Real (Fin (n + 1)))}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hU : IsOpen U) (hu : ContDiffOn Real 1 u (U ∩ {x | a ≤ x 0}))
    (hcs : HasCompactSupport u) (hsupp : tsupport u ∩ {x | a ≤ x 0} ⊆ U) :
    ∫ x in U ∩ {x | a < x 0},
        LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real u (U ∩ {x | a ≤ x 0}) x).toLinearMap
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  have h := integral_trace_fderivWithin_euclidean_half_space_of_hasCompactSupport
    (hu.contDiffOn_of_tsupport_subset hU hsupp) hcs
  rw [← Measure.restrict_restrict hU.measurableSet, ← integral_indicator
    hU.measurableSet]
  refine (integral_congr_ae ?_).trans h
  have hopen : IsOpen {x : EuclideanSpace Real (Fin (n + 1)) | a < x 0} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU, inter_comm U, fderivWithin_inter (hU.mem_nhds hxU)]
  · rw [indicator_of_notMem hxU]
    have hxcs : x ∉ tsupport u := fun hxcs =>
      hxU (hsupp ⟨hxcs, show a ≤ x 0 from le_of_lt hx⟩)
    have hnhds : {x : EuclideanSpace Real (Fin (n + 1)) | a ≤ x 0} ∈ 𝓝 x :=
      mem_of_superset (hopen.mem_nhds hx) (fun y hy => show a ≤ y 0 from le_of_lt hy)
    rw [fderivWithin_of_mem_nhds hnhds, fderiv_of_notMem_tsupport Real hxcs]
    simp

theorem integral_mul_trace_fderivWithin_add_fderivWithin_withDensity_euclidean_half_space_inter_of_hasCompactSupport
    {n : Nat} {a : Real}
    {U : Set (EuclideanSpace Real (Fin (n + 1)))}
    {phi rho : EuclideanSpace Real (Fin (n + 1)) → Real}
    {u : EuclideanSpace Real (Fin (n + 1)) → EuclideanSpace Real (Fin (n + 1))}
    (hU : IsOpen U) (hphi : ContDiffOn Real 1 phi (U ∩ {x | a ≤ x 0}))
    (hrho : AEMeasurable rho
      ((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict (U ∩ {x | a < x 0})))
    (hu : ContDiffOn Real 1 (fun x => rho x • u x) (U ∩ {x | a ≤ x 0}))
    (hpos : ∀ᵐ x ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
      (U ∩ {x | a < x 0})), 0 < rho x)
    (hcs : HasCompactSupport (fun x => phi x • (rho x • u x)))
    (hsupp : tsupport (fun x => phi x • (rho x • u x)) ∩ {x | a ≤ x 0} ⊆ U) :
    ∫ x, phi x *
        (LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real (fun y => rho y • u y) (U ∩ {x | a ≤ x 0}) x).toLinearMap /
            rho x) + fderivWithin Real phi (U ∩ {x | a ≤ x 0}) x (u x)
        ∂((modelHaar (E := EuclideanSpace Real (Fin (n + 1)))).restrict
          (U ∩ {x | a < x 0})).withDensity (fun x => ENNReal.ofReal (rho x)) =
      -((Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) volume •
        ∫ z : Fin n → Real, phi (WithLp.toLp 2 (Fin.cons a z)) *
          rho (WithLp.toLp 2 (Fin.cons a z)) * u (WithLp.toLp 2 (Fin.cons a z)) 0) := by
  have h := integral_trace_fderivWithin_euclidean_half_space_inter_of_hasCompactSupport
    hU (hphi.smul hu) hcs hsupp
  rw [integral_withDensity_eq_integral_toReal_smul₀ hrho.ennreal_ofReal
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top) _]
  have heq : (∫ x in U ∩ {x | a < x 0}, rho x •
      (phi x * (LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
        (fderivWithin Real (fun y => rho y • u y) (U ∩ {x | a ≤ x 0}) x).toLinearMap /
          rho x) + fderivWithin Real phi (U ∩ {x | a ≤ x 0}) x (u x))
      ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1))))) =
      ∫ x in U ∩ {x | a < x 0},
        LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
          (fderivWithin Real (fun y => phi y • (rho y • u y))
            (U ∩ {x | a ≤ x 0}) x).toLinearMap
        ∂(modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) := by
    apply integral_congr_ae
    have hopen : IsOpen (U ∩ {x : EuclideanSpace Real (Fin (n + 1)) | a < x 0}) :=
      hU.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
    filter_upwards [hpos, ae_restrict_mem hopen.measurableSet] with x hx hxU
    have hxs : x ∈ U ∩ {x : EuclideanSpace Real (Fin (n + 1)) | a ≤ x 0} :=
      ⟨hxU.1, show a ≤ x 0 from le_of_lt hxU.2⟩
    have hdiff : UniqueDiffWithinAt Real
        (U ∩ {x : EuclideanSpace Real (Fin (n + 1)) | a ≤ x 0}) x :=
      (hopen.uniqueDiffWithinAt hxU).mono
        (fun y hy => ⟨hy.1, show a ≤ y 0 from le_of_lt hy.2⟩)
    rw [fderivWithin_fun_smul hdiff (hphi.differentiableOn one_ne_zero x hxs)
      (hu.differentiableOn one_ne_zero x hxs)]
    change _ = LinearMap.trace Real (EuclideanSpace Real (Fin (n + 1)))
      (phi x • (fderivWithin Real (fun y => rho y • u y) (U ∩ {x | a ≤ x 0}) x).toLinearMap +
        (fderivWithin Real phi (U ∩ {x | a ≤ x 0}) x).toLinearMap.smulRight (rho x • u x))
    rw [map_add, map_smul, LinearMap.trace_smulRight, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, mul_add]
    congr 1
    rw [mul_left_comm, mul_div_cancel₀ _ hx.ne']
  calc
    _ = _ := integral_congr_ae (by
      filter_upwards [hpos] with x hx
      rw [ENNReal.toReal_ofReal hx.le])
    _ = _ := heq
    _ = _ := by simpa only [Pi.smul_def', PiLp.smul_apply, smul_eq_mul, mul_assoc] using h

end DifferentialGeometry.Analysis
