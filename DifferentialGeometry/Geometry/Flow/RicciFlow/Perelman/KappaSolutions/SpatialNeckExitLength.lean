import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCurveLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphPartial

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem exists_first_exit_of_leaves
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1))
    (h0 : γ 0 ∈ interior K) (hleave : ∃ u ∈ Icc (0 : ℝ) 1, γ u ∉ K) :
    ∃ t : ℝ, t ∈ Ioc 0 1 ∧ (∀ s ∈ Icc 0 t, γ s ∈ K) ∧ γ t ∈ frontier K := by
  let T := Icc (0 : ℝ) 1
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let γT : T → X := fun t => γ t
  let B : Set T := γT ⁻¹' (interior K)ᶜ
  have hγT : Continuous γT := hγ.domRestrict
  have hBclosed : IsClosed B := isOpen_interior.isClosed_compl.preimage hγT
  obtain ⟨u, hu, huleave⟩ := hleave
  have hBne : B.Nonempty := ⟨⟨u, hu⟩, fun h => huleave (interior_subset h)⟩
  obtain ⟨t, htB, htmin⟩ :=
    hBclosed.isCompact.exists_isMinOn hBne continuous_subtype_val.continuousOn
  have htNot : γ (t : ℝ) ∉ interior K := htB
  have htne : (t : ℝ) ≠ 0 := by
    intro ht
    apply htNot
    simpa only [ht] using h0
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.property.1 (Ne.symm htne)
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t, γ s ∈ interior K := by
    intro s hs
    by_contra hsNot
    let sT : T := ⟨s, hs.1, hs.2.le.trans t.property.2⟩
    have hsB : sT ∈ B := hsNot
    exact (not_le_of_gt hs.2) (htmin hsB)
  have htClosure : (t : ℝ) ∈ closure (Ico (0 : ℝ) t) := by
    rw [closure_Ico (Ne.symm htne)]
    exact ⟨htpos.le, le_rfl⟩
  have hcont : ContinuousWithinAt γ (Ico (0 : ℝ) t) t :=
    (hγ t t.property).mono (fun s hs => ⟨hs.1, hs.2.le.trans t.property.2⟩)
  have htK : γ t ∈ K := by
    have hclosure := hcont.mem_closure htClosure
      (fun s hs => interior_subset (hbefore s hs))
    simpa only [hK.closure_eq] using hclosure
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, ?_⟩
  · intro s hs
    by_cases hst : s = t
    · simpa only [hst] using htK
    · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
  · rw [frontier, hK.closure_eq]
    exact ⟨htK, htNot⟩

private local instance neckExitSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance neckExitC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

theorem length_gt_of_leaves_core (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x0 : spatialNeckBuffer epsilon) (hx0 : |x0.val.2| ≤ 5 * Real.pi)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hstart : γ 0 = W.embedding x0)
    (hleave : ∃ u ∈ Icc (0 : ℝ) 1, γ u ∉ W.core) :
    ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p) <
      metricPathELength (I := I) h γ 0 1 := by
  let _ : Nonempty (spatialNeckBuffer epsilon) := ⟨x0⟩
  have hdim : Module.finrank ℝ ((EuclideanSpace ℝ (Fin 2)) × ℝ) =
      Module.finrank ℝ E := by simpa [Module.finrank_prod] using W.dimension_three.symm
  have hlocal : IsLocalDiffeomorph SpatialNeckCylinderModel I ∞ W.embedding := fun x =>
    immersionAt_isLocalDiffeomorphAt_of_finrank_eq hdim
      (W.smooth_embedding.isImmersion.isImmersionAt x)
  let F := partialDiffeomorphOfInjectiveLocalDiffeomorph W.embedding hlocal
    W.smooth_embedding.isEmbedding.injective
  have hFsource : F.source = univ := partialDiffeomorphOfInjectiveLocalDiffeomorph_source _ _ _
  have hFtarget : F.target = W.image :=
    partialDiffeomorphOfInjectiveLocalDiffeomorph_target _ _ _
  have hleft (x : spatialNeckBuffer epsilon) : F.symm (W.embedding x) = x := by
    change F.symm (F x) = x
    exact F.toPartialEquiv.left_inv (by rw [hFsource]; trivial)
  have hKc : IsCompact W.core :=
    (spatialNeckClosedCore_isCompact epsilon).image W.embedding.continuous
  have hKtarget : W.core ⊆ F.target := by
    rw [hFtarget]
    rintro z ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  let V : Set (spatialNeckBuffer epsilon) :=
    {x | -epsilon⁻¹ < x.val.2 ∧ x.val.2 < epsilon⁻¹}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const)
  have hVcore : V ⊆ spatialNeckClosedCore epsilon := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  have hVint : W.embedding '' V ⊆ interior W.core :=
    interior_maximal (image_mono hVcore) (W.embedding_isOpenEmbedding.isOpenMap V hVopen)
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hx0V : x0 ∈ V := by
    have hx := abs_le.mp hx0
    change -epsilon⁻¹ < x0.val.2 ∧ x0.val.2 < epsilon⁻¹
    constructor <;> linarith [Real.pi_pos]
  have h0 : γ 0 ∈ interior W.core := by
    rw [hstart]
    exact hVint ⟨x0, hx0V, rfl⟩
  obtain ⟨t, ht, hstay, hfront⟩ :=
    exists_first_exit_of_leaves hKc.isClosed hγ.continuousOn h0 hleave
  have hfrontNot : γ t ∉ interior W.core := hfront.2
  let β : ℝ → spatialNeckBuffer epsilon := (F.symm : N → spatialNeckBuffer epsilon) ∘ γ
  have hβcore : ∀ s ∈ Icc (0 : ℝ) t, β s ∈ spatialNeckClosedCore epsilon := by
    intro s hs
    obtain ⟨x, hx, hxeq⟩ := hstay s hs
    change F.symm (γ s) ∈ spatialNeckClosedCore epsilon
    rw [← hxeq, hleft]
    exact hx
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (Icc 0 t) :=
    (F.contMDiffOn_invFun.of_le (by simp)).comp
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) (fun s hs => hKtarget (hstay s hs))
  have hβ0 : β 0 = x0 := by
    change F.symm (γ 0) = x0
    rw [hstart, hleft]
  have hright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : W.embedding (β s) = γ s :=
    F.toPartialEquiv.right_inv (hKtarget (hstay s hs))
  have hβtNot : β t ∉ V := by
    intro htV
    apply hfrontNot
    exact hVint ⟨β t, htV, hright t ⟨ht.1.le, le_rfl⟩⟩
  have habsExit : |(β t).val.2| = epsilon⁻¹ := by
    have hbounds := hβcore t ⟨ht.1.le, le_rfl⟩
    apply le_antisymm (abs_le.mpr hbounds)
    apply le_of_not_gt
    intro habs
    exact hβtNot (abs_lt.mp habs)
  have hdelta : 12 * Real.pi < |(β t).val.2 - x0.val.2| := by
    have hvar := abs_sub_abs_le_abs_sub (β t).val.2 x0.val.2
    rw [habsExit] at hvar
    linarith
  have hlengthEq : metricPathELength (I := I) h
      ((W.embedding : spatialNeckBuffer epsilon → N) ∘ β) 0 t =
      metricPathELength (I := I) h γ 0 t := by
    let _ : RiemannianBundle (fun z : N => TangentSpace I z) := ⟨h.toRiemannianMetric⟩
    change Manifold.pathELength I _ 0 t = Manifold.pathELength I _ 0 t
    exact Manifold.pathELength_congr hright
  have hlower := W.axial_displacement_le_pathELength hsmall ht.1.le hβ hβcore
  rw [hlengthEq, hβ0] at hlower
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hstrict : 11 * Real.pi * spatialNeckScale h p <
      11 / 12 * spatialNeckScale h p * |(β t).val.2 - x0.val.2| := by
    have hmul := mul_lt_mul_of_pos_left hdelta
      (by positivity : 0 < 11 / 12 * spatialNeckScale h p)
    nlinarith
  have hENN := (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by positivity) hstrict)).mpr hstrict
  exact (hENN.trans_le hlower).trans_le (metricPathELength_mono h γ le_rfl ht.2)

theorem short_curve_stays_core (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x0 : spatialNeckBuffer epsilon) (hx0 : |x0.val.2| ≤ 5 * Real.pi)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hstart : γ 0 = W.embedding x0)
    (hlen : metricPathELength (I := I) h γ 0 1 ≤
      ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p)) :
    ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ W.core := by
  intro u hu
  by_contra hnot
  exact not_lt_of_ge hlen
    (W.length_gt_of_leaves_core hsmall x0 hx0 hγ hstart ⟨u, hu, hnot⟩)

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
