import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspAngleComparison
import DifferentialGeometry.Analysis.Integration.Measure.Boundary
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

/-!
# Volume transfer through a cusp collar (statement V.1)

For a cusp embedding `e : CuspEmbedding W g K δ X` (`0 ≤ δ < 1`) and a Borel set `S ⊆ T² × [0, 100)`:

`(1 - δ)^{3/2} μ_H(S) ≤ vol_g(e(S)) ≤ (1 + δ)^{3/2} μ_H(S)`,  `dμ_H = e^{-z} dA_{g_T} dz`

(`CuspEmbedding.volume_transfer`, the interface `V_volume_transfer` verbatim).

Proof (design D4). One half-open fundamental domain: `cuspAngleSet S` is the set of `v ∈ ℝ³` with
angles in `(-π, π]²` and `cuspAngleParam v ∈ S`.
* Measure side (`setLIntegral_cuspAngleSet_eq`): `μ_H(S) = ∫_{cuspAngleSet S} c e^{-v₂} ρ_T dmodelHaar`
  — the torus area in angle coordinates (`riemannianVolumeMeasure_torus_eq_map`), `map_prod_map`,
  `prod_withDensity_left`, and the Haar normalisation `smul_modelHaar_eq_map_prod` with the same
  constant `c` as the density.
* Positive heights (`CuspEmbedding.volume_transfer_of_pos`): the injective `C¹` area formula for
  `Ψ = e ∘ cuspAngleParam` on `cuspAngleSet S` and the pointwise density comparison
  `CuspEmbedding.paramDensity_cuspAngle_bounds`.
* Height `0`: the slice `T² × {0}` is `μ_H`-null (product with a Lebesgue-null set) and its image
  lies in `∂W` (`boundary_preimage`), which is `vol_g`-null
  (`CompactCarrier.riemannianVolumeMeasure_boundary_eq_zero`). V.1 is not used circularly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry DifferentialGeometry.Integral.Measure GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

local notation "E₂" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance instMeasE₂ : MeasurableSpace E₂ := borel E₂
private local instance instBorelE₂ : BorelSpace E₂ := ⟨rfl⟩
private local instance instMeasE₃ : MeasurableSpace E₃ := borel E₃
private local instance instBorelE₃ : BorelSpace E₃ := ⟨rfl⟩
private local instance instMeasTorus : MeasurableSpace Torus := borel Torus
private local instance instBorelTorus : BorelSpace Torus := ⟨rfl⟩

/-- The angle-coordinate preimage of `S ⊆ T² × ℝ` over the fundamental domain `(-π, π]²`. -/
def cuspAngleSet (S : Set (Torus × ℝ)) : Set E₃ :=
  {v | (cuspCoordEquiv v).1 ∈ torusAngleDomain ∧
    (torusAngleParam (cuspCoordEquiv v).1, v 2) ∈ S}

theorem measurableSet_prod_of_borel {S : Set (Torus × ℝ)}
    (hS : MeasurableSet[borel (Torus × ℝ)] S) : MeasurableSet S := by
  rwa [BorelSpace.measurable_eq (α := Torus × ℝ)]

theorem measurable_prodMap_torusAngleParam :
    Measurable (Prod.map torusAngleParam id : E₂ × ℝ → Torus × ℝ) :=
  measurable_torusAngleParam.prodMap measurable_id

theorem cuspAngleSet_eq_preimage (S : Set (Torus × ℝ)) :
    cuspAngleSet S = cuspCoordEquiv ⁻¹'
      (Prod.map torusAngleParam id ⁻¹' S ∩ torusAngleDomain ×ˢ univ) := by
  ext v
  simp only [cuspAngleSet, mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
    cuspCoordEquiv_apply_snd]
  exact and_comm

theorem measurableSet_cuspAngleSet {S : Set (Torus × ℝ)}
    (hS : MeasurableSet[borel (Torus × ℝ)] S) : MeasurableSet (cuspAngleSet S) := by
  rw [cuspAngleSet_eq_preimage]
  exact cuspCoordEquiv.continuous.measurable
    ((measurable_prodMap_torusAngleParam (measurableSet_prod_of_borel hS)).inter
      (measurableSet_torusAngleDomain.prod MeasurableSet.univ))

theorem preimage_cuspAngleSet (S : Set (Torus × ℝ)) :
    cuspCoordEquiv.symm ⁻¹' cuspAngleSet S =
      Prod.map torusAngleParam id ⁻¹' S ∩ torusAngleDomain ×ˢ univ := by
  rw [cuspAngleSet_eq_preimage, ← preimage_comp]
  simp

/-- **The cusp measure in angle coordinates (V.1, step 5, measure side).** -/
theorem setLIntegral_cuspAngleSet_eq (gT : SmoothRiemannianMetric torusModel Torus)
    {S : Set (Torus × ℝ)} (hS : MeasurableSet[borel (Torus × ℝ)] S) :
    ∫⁻ v in cuspAngleSet S, ENNReal.ofReal (cuspAngleConstant * (Real.exp (-v 2) *
        paramDensity gT torusAngleParam (cuspCoordEquiv v).1)) ∂(modelHaar (E := E₃)) =
      ((@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
        volume).withDensity fun p => ENNReal.ofReal (Real.exp (-p.2))) S := by
  set ρ : E₂ → ℝ := paramDensity gT torusAngleParam with hρ
  have hρc : Continuous ρ := continuous_paramDensity_torusAngleParam gT
  set F : E₂ × ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (-w.2) * ρ w.1) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp continuous_snd.neg).mul (hρc.comp continuous_fst)).measurable
  have hS' := measurableSet_prod_of_borel hS
  have hK := measurableSet_cuspAngleSet hS
  -- the source side
  have hL : ∫⁻ v in cuspAngleSet S, ENNReal.ofReal (cuspAngleConstant * (Real.exp (-v 2) *
      ρ (cuspCoordEquiv v).1)) ∂(modelHaar (E := E₃)) =
      ∫⁻ w in Prod.map torusAngleParam id ⁻¹' S ∩ torusAngleDomain ×ˢ univ, F w
        ∂((modelHaar (E := E₂)).prod volume) := by
    rw [← preimage_cuspAngleSet, ← setLIntegral_smul_modelHaar_eq hK hFm, Measure.restrict_smul,
      lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun v => ?_
    rw [ENNReal.ofReal_mul cuspAngleConstant_nonneg]
    rfl
  -- the target side
  have hμ0 : @Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
      volume = Measure.map (Prod.map torusAngleParam id)
        ((((modelHaar (E := E₂)).restrict torusAngleDomain).withDensity
          fun u => ENNReal.ofReal (ρ u)).prod volume) := by
    rw [riemannianVolumeMeasure_torus_eq_map gT, ← Measure.map_prod_map _ _ measurable_torusAngleParam
      measurable_id, Measure.map_id (μ := (volume : Measure ℝ))]
  have hρm : Measurable fun u => ENNReal.ofReal (ρ u) :=
    ENNReal.measurable_ofReal.comp hρc.measurable
  have hρm1 : Measurable fun w : E₂ × ℝ => ENNReal.ofReal (ρ w.1) :=
    ENNReal.measurable_ofReal.comp (hρc.comp continuous_fst).measurable
  have hexpm : Measurable fun p : Torus × ℝ => ENNReal.ofReal (Real.exp (-p.2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp continuous_snd.neg).measurable
  have hexpm' : Measurable fun w : E₂ × ℝ => ENNReal.ofReal (Real.exp (-w.2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp continuous_snd.neg).measurable
  have hν : (((modelHaar (E := E₂)).restrict torusAngleDomain).withDensity
      fun u => ENNReal.ofReal (ρ u)).prod (volume : Measure ℝ) =
      (((modelHaar (E := E₂)).prod volume).restrict (torusAngleDomain ×ˢ univ)).withDensity
        fun w => ENNReal.ofReal (ρ w.1) := by
    rw [prod_withDensity_left hρm, Measure.restrict_prod_eq_prod_univ]
  have hpre := measurable_prodMap_torusAngleParam hS'
  rw [hL, withDensity_apply _ hS', hμ0, setLIntegral_map hS' hexpm
    measurable_prodMap_torusAngleParam, hν, setLIntegral_withDensity_eq_setLIntegral_mul _
      (g := fun x => ENNReal.ofReal (Real.exp (-(Prod.map torusAngleParam id x).2))) hρm1 hexpm' hpre, Measure.restrict_restrict hpre]
  refine lintegral_congr fun w => ?_
  simp only [hF, Pi.mul_apply]
  change ENNReal.ofReal (Real.exp (-w.2) * ρ w.1) =
    ENNReal.ofReal (ρ w.1) * ENNReal.ofReal (Real.exp (-w.2))
  rw [mul_comm]
  exact ENNReal.ofReal_mul (Real.sqrt_nonneg _)

universe u

theorem image_lift_eq_image_cuspAngleSet (S : Set (Torus × ℝ)) :
    (fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S = cuspAngleParam '' cuspAngleSet S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨u, hu, hut⟩ := exists_mem_torusAngleDomain_eq p.1
    refine ⟨cuspCoordEquiv.symm (u, p.2), ?_, ?_⟩
    · change (cuspCoordEquiv (cuspCoordEquiv.symm (u, p.2))).1 ∈ torusAngleDomain ∧
        (torusAngleParam (cuspCoordEquiv (cuspCoordEquiv.symm (u, p.2))).1,
          (cuspCoordEquiv (cuspCoordEquiv.symm (u, p.2))).2) ∈ S
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨hu, by rw [hut]; exact hp⟩
    · change (torusAngleParam (cuspCoordEquiv (cuspCoordEquiv.symm (u, p.2))).1,
        halfSpaceOneLift (cuspCoordEquiv (cuspCoordEquiv.symm (u, p.2))).2) = _
      rw [ContinuousLinearEquiv.apply_symm_apply, hut]
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(torusAngleParam (cuspCoordEquiv v).1, v 2), hv.2, rfl⟩

theorem halfSpaceOneLift_injOn_Ici : InjOn halfSpaceOneLift (Ici (0 : ℝ)) := by
  intro s hs t ht h
  have h' := congrArg (fun q : EuclideanHalfSpace 1 => q.val 0) h
  change max s 0 = max t 0 at h'
  rwa [max_eq_left hs, max_eq_left ht] at h'

theorem injOn_cuspAngleParam :
    InjOn cuspAngleParam {v : E₃ | (cuspCoordEquiv v).1 ∈ torusAngleDomain ∧ 0 ≤ v 2} := by
  intro v hv v' hv' h
  simp only [cuspAngleParam, Prod.mk.injEq] at h
  have h1 := injOn_torusAngleParam hv.1 hv'.1 h.1
  have h2 := halfSpaceOneLift_injOn_Ici hv.2 hv'.2 h.2
  apply cuspCoordEquiv.injective
  exact Prod.ext h1 h2

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- **V.1 at positive heights.** -/
theorem CuspEmbedding.volume_transfer_of_pos (e : CuspEmbedding W g K δ X) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) {S : Set (Torus × ℝ)} (hS : MeasurableSet[borel (Torus × ℝ)] S)
    (hSd : ∀ p ∈ S, 0 < p.2 ∧ p.2 < cuspDepth) :
    ENNReal.ofReal ((1 - δ) ^ ((3 : ℝ) / 2)) *
        ((@Measure.prod Torus ℝ (borel Torus) _
          (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) volume).withDensity
            fun p => ENNReal.ofReal (Real.exp (-p.2))) S ≤
        riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S)) ∧
      riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
        ((@Measure.prod Torus ℝ (borel Torus) _
          (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) volume).withDensity
            fun p => ENNReal.ofReal (Real.exp (-p.2))) S := by
  set gT := e.cusp.torusMetric
  set KS := cuspAngleSet S with hKSdef
  set U : Set E₃ := {v | 0 < v 2 ∧ v 2 < cuspDepth} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun v : E₃ => v 2)).inter
      (isOpen_lt (by fun_prop : Continuous fun v : E₃ => v 2) continuous_const)
  have hKU : KS ⊆ U := fun v hv => hSd _ hv.2
  have hKm : MeasurableSet KS := measurableSet_cuspAngleSet hS
  have hΨ : ContMDiffOn 𝓘(ℝ, E₃) W.model 1 (e.toFun ∘ cuspAngleParam) U :=
    (e.contMDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 K)).comp
      ((contMDiffOn_cuspAngleParam.mono fun v hv => hv.1.le).of_le (by exact_mod_cast le_top))
      fun v hv => cuspAngleParam_mem_cuspDomain hv.2
  have hinj : InjOn (e.toFun ∘ cuspAngleParam) KS := by
    intro v hv v' hv' h
    have hvU := hKU hv
    have hv'U := hKU hv'
    have h1 : cuspAngleParam v = cuspAngleParam v' :=
      congrArg Subtype.val (e.isEmbedding.injective
        (a₁ := ⟨_, cuspAngleParam_mem_cuspDomain hvU.2⟩)
        (a₂ := ⟨_, cuspAngleParam_mem_cuspDomain hv'U.2⟩) h)
    exact injOn_cuspAngleParam ⟨hv.1, hvU.1.le⟩ ⟨hv'.1, hv'U.1.le⟩ h1
  have hT : e.toFun '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S) =
      (e.toFun ∘ cuspAngleParam) '' KS := by
    rw [image_lift_eq_image_cuspAngleSet, image_comp]
  have hvol := riemannianVolumeMeasure_image_eq g hUo hKm hKU hΨ hinj
  have hμ := setLIntegral_cuspAngleSet_eq gT hS
  rw [hT, hvol, ← hμ]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hKm fun v hv => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (sub_nonneg.mpr hδ.le) _)]
    exact ENNReal.ofReal_le_ofReal (e.paramDensity_cuspAngle_bounds hδ0 hδ (hKU hv).1 (hKU hv).2).1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hKm fun v hv => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    exact ENNReal.ofReal_le_ofReal (e.paramDensity_cuspAngle_bounds hδ0 hδ (hKU hv).1 (hKU hv).2).2

theorem riemannianVolumeMeasure_boundary_carrierModel_eq_zero (k : CarrierModel) {M : Type*}
    [TopologicalSpace M] [ChartedSpace k.Space M] [IsManifold k.model ∞ M] [T2Space M]
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric k.model M) :
    riemannianVolumeMeasure k.model M g (k.model.boundary M) = 0 := by
  cases k with
  | closed =>
    have h : (CarrierModel.closed.model).boundary M = ∅ :=
      ModelWithCorners.Boundaryless.boundary_eq_empty
    rw [h, measure_empty]
  | withBoundary => exact riemannianVolumeMeasure_boundary_eq_zero g

/-- The boundary of a compact carrier is a Riemannian null set. -/
theorem CompactCarrier.riemannianVolumeMeasure_boundary_eq_zero (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) :
    riemannianVolumeMeasure W.model W.Carrier g (W.model.boundary W.Carrier) = 0 :=
  riemannianVolumeMeasure_boundary_carrierModel_eq_zero W.kind g

theorem measurableSet_borel_of_prod {S : Set (Torus × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet[borel (Torus × ℝ)] S := by
  rwa [BorelSpace.measurable_eq (α := Torus × ℝ)] at hS

/-- The height-`0` slice is null for the cusp measure. -/
theorem cuspMeasure_height_zero_eq_zero (gT : SmoothRiemannianMetric torusModel Torus)
    {S : Set (Torus × ℝ)} (hS : ∀ p ∈ S, p.2 = 0) :
    ((@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
        volume).withDensity fun p => ENNReal.ofReal (Real.exp (-p.2))) S = 0 := by
  have hsub : S ⊆ univ ×ˢ {0} := fun p hp => ⟨mem_univ _, hS p hp⟩
  have h0 : (@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
      volume) (univ ×ˢ {0}) = 0 := by
    rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
  exact withDensity_absolutelyContinuous _ _ (measure_mono_null hsub h0)

/-- **Volume transfer through a cusp collar (statement V.1).** For a Borel set `S` of heights in
`[0, 100)`, `vol_g(e(S))` is the cusp measure `μ_H(S)`, `dμ_H = e^{-z} dA_{g_T} dz`, up to the factors
`(1 ∓ δ)^{3/2}`. -/
theorem CuspEmbedding.volume_transfer (e : CuspEmbedding W g K δ X) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    {S : Set (Torus × ℝ)} (hS : MeasurableSet[borel (Torus × ℝ)] S)
    (hSd : ∀ p ∈ S, 0 ≤ p.2 ∧ p.2 < cuspDepth) :
    let μH := (@Measure.prod Torus ℝ (borel Torus) _
      (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) volume).withDensity
        fun p => ENNReal.ofReal (Real.exp (-p.2))
    let T : Set W.Carrier := e.toFun '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S)
    ENNReal.ofReal ((1 - δ) ^ ((3 : ℝ) / 2)) * μH S ≤
        riemannianVolumeMeasure W.model W.Carrier g T ∧
      riemannianVolumeMeasure W.model W.Carrier g T ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) * μH S := by
  intro μH T
  set L : Torus × ℝ → CuspHalfSpace := fun p => (p.1, halfSpaceOneLift p.2) with hL
  set Sp := S ∩ {p : Torus × ℝ | 0 < p.2} with hSp
  set S0 := S ∩ {p : Torus × ℝ | p.2 = 0} with hS0
  have hSp_m : MeasurableSet[borel (Torus × ℝ)] Sp :=
    measurableSet_borel_of_prod ((measurableSet_prod_of_borel hS).inter
      (measurableSet_lt measurable_const measurable_snd))
  have hpos := e.volume_transfer_of_pos hδ0 hδ hSp_m fun p hp => ⟨hp.2, (hSd p hp.1).2⟩
  have hsplit : S ⊆ Sp ∪ S0 := by
    intro p hp
    rcases (hSd p hp).1.lt_or_eq with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h.symm⟩
  have hμ0 : μH S0 = 0 := cuspMeasure_height_zero_eq_zero _ fun p hp => hp.2
  have hμ : μH S = μH Sp := by
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc μH S ≤ μH (Sp ∪ S0) := measure_mono hsplit
      _ ≤ μH Sp + μH S0 := measure_union_le _ _
      _ = μH Sp := by rw [hμ0, add_zero]
  have hT0 : e.toFun '' (L '' S0) ⊆ W.model.boundary W.Carrier := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have hd : L p ∈ cuspDomain := by
      change max p.2 0 < cuspDepth
      rw [hp.2, max_self]
      norm_num [cuspDepth]
    refine (e.boundary_preimage hd).mpr ?_
    change max p.2 0 = 0
    rw [hp.2, max_self]
  have hvol0 : riemannianVolumeMeasure W.model W.Carrier g (e.toFun '' (L '' S0)) = 0 :=
    measure_mono_null hT0 (CompactCarrier.riemannianVolumeMeasure_boundary_eq_zero W g)
  have hTsplit : T ⊆ e.toFun '' (L '' Sp) ∪ e.toFun '' (L '' S0) := by
    rw [← image_union, ← image_union]
    exact image_mono (image_mono hsplit)
  have hTp : e.toFun '' (L '' Sp) ⊆ T := image_mono (image_mono inter_subset_left)
  have hvol : riemannianVolumeMeasure W.model W.Carrier g T =
      riemannianVolumeMeasure W.model W.Carrier g (e.toFun '' (L '' Sp)) := by
    refine le_antisymm ?_ (measure_mono hTp)
    calc riemannianVolumeMeasure W.model W.Carrier g T
        ≤ riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' (L '' Sp) ∪ e.toFun '' (L '' S0)) := measure_mono hTsplit
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hvol0, add_zero]
  rw [hμ, hvol]
  exact hpos

end DifferentialGeometry.Geometry.Collapse
