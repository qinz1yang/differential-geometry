import DifferentialGeometry.Topology.VectorField.CollarNormalization

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Poincare.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def normalizedCollarExtension
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ)
    (p : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p :=
  if p.2 ≤ 0 then collarNormalization V ε 1 p else
    collarExtension (fun x => (V (x, 0)).1) (fun x => (V (x, 0)).2) collarTransition p


theorem normalizedCollarExtension_of_nonpos
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ)
    {p : M × ℝ} (hp : p.2 ≤ 0) :
    normalizedCollarExtension V ε p = collarNormalization V ε 1 p :=
  if_pos hp


theorem normalizedCollarExtension_of_pos
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ)
    {p : M × ℝ} (hp : 0 < p.2) :
    normalizedCollarExtension V ε p =
      collarExtension (fun x => (V (x, 0)).1) (fun x => (V (x, 0)).2) collarTransition p :=
  if_neg hp.not_ge

theorem collarNormalization_eventuallyEq_collarExtension
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) {ε : ℝ}
    (hε : 0 < ε) {p : M × ℝ} (hp : p.2 = 0) :
    (fun q => (⟨q, collarNormalization V ε 1 q⟩ :
      TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) =ᶠ[𝓝 p]
    (fun q => (⟨q, collarExtension (fun x => (V (x, 0)).1)
      (fun x => (V (x, 0)).2) collarTransition q⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hnear : ∀ᶠ q : M × ℝ in 𝓝 p, -ε / 3 < q.2 ∧ q.2 < 1 / 3 :=
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)).mem_nhds (by
        change -ε / 3 < p.2 ∧ p.2 < 1 / 3
        rw [hp]
        constructor <;> linarith)
  filter_upwards [hnear] with q hq
  apply congrArg (fun z : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q =>
    (⟨q, z⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))
  exact (collarNormalization_one_eq_boundary V hε hq.1.le).trans
    (collarExtension_eq_boundaryPair (I := I) (fun x => (V (x, 0)).1)
      (fun x => (V (x, 0)).2) hq.2.le).symm

private theorem contMDiff_boundaryExtension [IsManifold I 1 M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, collarExtension (fun x => (V (x, 0)).1)
        (fun x => (V (x, 0)).2) collarTransition p⟩ :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hslice : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun x : M => (x, (0 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  have hcomponents := contMDiff_equivTangentBundleProd.comp (hV.comp hslice)
  exact contMDiff_collarExtension hcomponents.fst
    ((contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hcomponents.snd)
    contDiff_collarTransition


theorem contMDiff_normalizedCollarExtension [IsManifold I 1 M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, normalizedCollarExtension V ε p⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have h := (contMDiff_collarNormalization hV ε 1).piecewise
    (s := {p : M × ℝ | p.2 ≤ 0}) (contMDiff_boundaryExtension hV) (fun p hp =>
      collarNormalization_eventuallyEq_collarExtension V hε (by
        have ht := continuous_snd.frontier_preimage_subset (Iic (0 : ℝ)) hp
        simpa using ht))
  convert h using 1
  funext p
  by_cases hp : p.2 ≤ 0 <;> simp [normalizedCollarExtension, Set.piecewise, hp]


theorem normalizedCollarExtension_boundary
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ) (x : M) :
    normalizedCollarExtension V ε (x, 0) = V (x, 0) := by
  rw [normalizedCollarExtension_of_nonpos V ε (by simp), collarNormalization_boundary]


theorem normalizedCollarExtension_eq_self
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) {ε : ℝ}
    (hε : 0 < ε) {p : M × ℝ} (hp : p.2 ≤ -(2 * ε / 3)) :
    normalizedCollarExtension V ε p = V p := by
  rw [normalizedCollarExtension_of_nonpos V ε (by linarith)]
  exact collarNormalization_eq_self V 1 hε hp


theorem normalizedCollarExtension_eq_outwardPair
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ)
    {p : M × ℝ} (hp : 2 / 3 ≤ p.2) :
    normalizedCollarExtension V ε p = ((V (p.1, 0)).1, (1 : ℝ)) := by
  rw [normalizedCollarExtension_of_pos V ε (by linarith)]
  exact collarExtension_eq_outwardPair _ _ hp

private theorem boundary_normal_ne_zero
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    {x : M} (hV : V (x, 0) ≠ 0) (hT : (V (x, 0)).1 = 0) :
    (V (x, 0)).2 ≠ 0 := by
  intro hb
  exact hV (Prod.ext hT hb)

theorem normalizedCollarExtension_eq_zero_iff
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε : ℝ}
    (hε : 0 < ε) (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    (p : M × ℝ) :
    normalizedCollarExtension V ε p = 0 ↔
      (p.2 ≤ 0 ∧ V p = 0) ∨
      (0 < p.2 ∧ (V (p.1, 0)).1 = 0 ∧ (V (p.1, 0)).2 < 0 ∧
        collarTransition p.2 = -(V (p.1, 0)).2 / (1 - (V (p.1, 0)).2)) := by
  by_cases hp : p.2 ≤ 0
  · rw [normalizedCollarExtension_of_nonpos V ε hp]
    simpa only [hp, true_and, not_lt_of_ge hp, false_and, or_false] using
      collarNormalization_eq_zero_iff hε hstrip (u := 1) (by constructor <;> norm_num) hp
  · rw [normalizedCollarExtension_of_pos V ε (lt_of_not_ge hp)]
    simpa only [hp, false_and, false_or, lt_of_not_ge hp, true_and] using!
      collarExtension_eq_zero_iff (I := I) (boundary_normal_ne_zero (I := I) (V := V)
        (hstrip p.1 0 ⟨by linarith, le_rfl⟩)) (collarTransition_mem_Icc p.2)


theorem normalizedCollarExtension_eventuallyEq_of_zero
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε : ℝ}
    (hε : 0 < ε) (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    {p : M × ℝ} (hp : V p = 0) (hp0 : p.2 ≤ 0) :
    (fun q => (⟨q, normalizedCollarExtension V ε q⟩ :
      TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) =ᶠ[𝓝 p]
      (fun q => (⟨q, V q⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hpt : p.2 < -ε := lt_of_not_ge (fun h => hstrip p.1 p.2 ⟨h, hp0⟩ hp)
  have hnear : ∀ᶠ q : M × ℝ in 𝓝 p, q.2 < -(2 * ε / 3) :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds (by
      change p.2 < -(2 * ε / 3)
      linarith)
  filter_upwards [hnear] with q hq
  exact congrArg (fun z : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q =>
    (⟨q, z⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))
    (normalizedCollarExtension_eq_self V hε hq.le)

theorem normalizedCollarExtension_zeroSet_proj_bijOn
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hboundary : ∀ x, V (x, 0) ≠ 0) (ε : ℝ) :
    BijOn Prod.fst {p : M × ℝ | 0 < p.2 ∧ normalizedCollarExtension V ε p = 0}
      {x : M | (V (x, 0)).1 = 0 ∧ (V (x, 0)).2 < 0} := by
  have hset : {p : M × ℝ | 0 < p.2 ∧ normalizedCollarExtension V ε p = 0} =
      {p : M × ℝ | collarExtension (I := I) (fun x => (V (x, 0)).1)
        (fun x => (V (x, 0)).2) collarTransition p = 0} := by
    ext p
    constructor
    · rintro ⟨ht, hz⟩
      rwa [normalizedCollarExtension_of_pos V ε ht] at hz
    · intro hz
      have ht := collarExtension_zero_height_mem_Ioo (I := I)
        (boundary_normal_ne_zero (I := I) (V := V) (hboundary p.1)) hz
      have hp : 0 < p.2 := by linarith [ht.1]
      exact ⟨hp, (normalizedCollarExtension_of_pos V ε hp).trans hz⟩
  rw [hset]
  exact collarExtension_zeroSet_proj_bijOn (I := I)
    (fun x => boundary_normal_ne_zero (I := I) (V := V) (hboundary x))

private theorem isolated_boundaryExtension_zero
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {p : M × ℝ}
    (hboundary : V (p.1, 0) ≠ 0)
    (hp : collarExtension (I := I) (fun x => (V (x, 0)).1)
      (fun x => (V (x, 0)).2) collarTransition p = 0)
    (hT : ∀ᶠ y in 𝓝 p.1, (V (y, 0)).1 = 0 → y = p.1) :
    ∀ᶠ q in 𝓝 p, collarExtension (I := I) (fun x => (V (x, 0)).1)
      (fun x => (V (x, 0)).2) collarTransition q = 0 → q = p := by
  have hz := (collarExtension_eq_zero_iff (I := I)
    (boundary_normal_ne_zero (I := I) (V := V) hboundary) (collarTransition_mem_Icc p.2)).mp hp
  obtain ⟨t, _, ht⟩ := existsUnique_collarExtension_eq_zero (I := I)
    (T := fun x => (V (x, 0)).1) (b := fun x => (V (x, 0)).2) hz.1 hz.2.1
  filter_upwards [(continuous_fst.tendsto p).eventually hT] with q hq
  intro hzero
  have hxy : q.1 = p.1 := hq (congrArg Prod.fst hzero)
  have hzero' : collarExtension (I := I) (fun x => (V (x, 0)).1)
      (fun x => (V (x, 0)).2) collarTransition (p.1, q.2) = 0 := by
    have hqp : (p.1, q.2) = q := Prod.ext hxy.symm rfl
    rw [hqp]
    exact hzero
  exact Prod.ext hxy ((ht q.2 hzero').trans (ht p.2 hp).symm)

theorem normalizedCollarExtension_isolated_zeros
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε : ℝ}
    (hε : 0 < ε) (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    (hinterior : ∀ p : M × ℝ, p.2 ≤ 0 → V p = 0 →
      ∀ᶠ q in 𝓝 p, V q = 0 → q = p)
    (htangent : ∀ x : M, (V (x, 0)).1 = 0 →
      ∀ᶠ y in 𝓝 x, (V (y, 0)).1 = 0 → y = x)
    (p : M × ℝ) (hp : normalizedCollarExtension V ε p = 0) :
    ∀ᶠ q in 𝓝 p, normalizedCollarExtension V ε q = 0 → q = p := by
  by_cases ht : p.2 ≤ 0
  · have hVp : V p = 0 := by
      have h := (normalizedCollarExtension_eq_zero_iff hε hstrip p).mp hp
      exact h.elim And.right (fun h => (not_lt_of_ge ht h.1).elim)
    filter_upwards [normalizedCollarExtension_eventuallyEq_of_zero hε hstrip hVp ht,
      hinterior p ht hVp] with q heq hq
    intro hz
    have heq' := TotalSpace.mk_injective q heq
    exact hq (heq'.symm.trans hz)
  · have htpos : 0 < p.2 := lt_of_not_ge ht
    rw [normalizedCollarExtension_of_pos V ε htpos] at hp
    have hT : (V (p.1, 0)).1 = 0 := congrArg Prod.fst hp
    have hiso := isolated_boundaryExtension_zero
      (hstrip p.1 0 ⟨by linarith, le_rfl⟩) hp (htangent p.1 hT)
    have hpos : ∀ᶠ q : M × ℝ in 𝓝 p, 0 < q.2 :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds htpos
    filter_upwards [hiso, hpos] with q hq hqt
    rw [normalizedCollarExtension_of_pos V ε hqt]
    exact hq

end Poincare.VectorField
