import DifferentialGeometry.Topology.InvarianceOfDomainManifold

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E F : Type*}

private def halfSpaceFold (p : E × ℝ) : E × Ici (0 : ℝ) :=
  (p.1, ⟨|p.2|, abs_nonneg p.2⟩)

private def halfSpaceDouble
    (f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)) (p : E × ℝ) : F × ℝ :=
  ((f (halfSpaceFold p)).1,
    if 0 ≤ p.2 then (f (halfSpaceFold p)).2.val else -(f (halfSpaceFold p)).2.val)

private theorem halfSpaceFold_inclusion (p : E × Ici (0 : ℝ)) :
    halfSpaceFold (p.1, p.2.val) = p := by
  refine Prod.ext ?_ ?_
  · rfl
  · apply Subtype.ext
    exact abs_of_nonneg p.2.property

private theorem halfSpaceDouble_inclusion
    (f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)) (p : E × Ici (0 : ℝ)) :
    halfSpaceDouble f (p.1, p.2.val) = ((f p).1, (f p).2.val) := by
  simp only [halfSpaceDouble, halfSpaceFold_inclusion]
  have hheight :
      (if 0 ≤ p.2.val then (f p).2.val else -(f p).2.val) = (f p).2.val :=
    ite_eq_left p.2.property
  rw [hheight]

private theorem halfSpaceFold_double
    (f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)) (p : E × ℝ) :
    halfSpaceFold (halfSpaceDouble f p) = f (halfSpaceFold p) := by
  refine Prod.ext ?_ ?_
  · rfl
  · apply Subtype.ext
    change |if 0 ≤ p.2 then (f (halfSpaceFold p)).2.val else -(f (halfSpaceFold p)).2.val| = _
    have hheight_nonneg : (0 : ℝ) ≤ (f (halfSpaceFold p)).2.val :=
      (f (halfSpaceFold p)).2.property
    split_ifs
    · exact abs_of_nonneg hheight_nonneg
    · rw [abs_neg]
      exact abs_of_nonneg hheight_nonneg

private theorem halfSpaceDouble_injOn
    {U : Set (E × Ici (0 : ℝ))}
    {f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)}
    (hinj : InjOn f U)
    (hboundary : ∀ x ∈ U, (f x).2.val = 0 ↔ x.2.val = 0) :
    InjOn (halfSpaceDouble f) (halfSpaceFold ⁻¹' U) := by
  intro p hp q hq hpq
  have hfold : halfSpaceFold p = halfSpaceFold q := by
    apply hinj hp hq
    simpa only [halfSpaceFold_double] using congrArg halfSpaceFold hpq
  have ht : |p.2| = |q.2| := congrArg (fun x : E × Ici (0 : ℝ) => x.2.val) hfold
  have hnormal :
      (if 0 ≤ p.2 then (f (halfSpaceFold p)).2.val else -(f (halfSpaceFold p)).2.val) =
      (if 0 ≤ q.2 then (f (halfSpaceFold q)).2.val else -(f (halfSpaceFold q)).2.val) :=
    congrArg Prod.snd hpq
  have hfheight : (f (halfSpaceFold p)).2.val = (f (halfSpaceFold q)).2.val :=
    congrArg (fun x : E × Ici (0 : ℝ) => (f x).2.val) hfold
  refine Prod.ext ?_ ?_
  · exact congrArg (fun z : E × Ici (0 : ℝ) => z.1) hfold
  · by_cases hpnonneg : 0 ≤ p.2
    · by_cases hqnonneg : 0 ≤ q.2
      · simpa only [abs_of_nonneg hpnonneg, abs_of_nonneg hqnonneg] using ht
      · simp only [hpnonneg, hqnonneg, reduceIte] at hnormal
        have hzero : (f (halfSpaceFold q)).2.val = 0 := by linarith
        have hqzero : q.2 = 0 := abs_eq_zero.mp ((hboundary _ hq).mp hzero)
        exact (hqnonneg (by rw [hqzero])).elim
    · by_cases hqnonneg : 0 ≤ q.2
      · simp only [hpnonneg, hqnonneg, reduceIte] at hnormal
        have hzero : (f (halfSpaceFold p)).2.val = 0 := by linarith
        have hpzero : p.2 = 0 := abs_eq_zero.mp ((hboundary _ hp).mp hzero)
        exact (hpnonneg (by rw [hpzero])).elim
      · have hpneg : p.2 ≤ 0 := (lt_of_not_ge hpnonneg).le
        have hqneg : q.2 ≤ 0 := (lt_of_not_ge hqnonneg).le
        rw [abs_of_nonpos hpneg, abs_of_nonpos hqneg] at ht
        exact neg_injective ht

private theorem image_eq_preimage_halfSpaceDouble
    (f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)) (U : Set (E × Ici (0 : ℝ))) :
    f '' U = (fun y : F × Ici (0 : ℝ) => (y.1, y.2.val)) ⁻¹'
      (halfSpaceDouble f '' (halfSpaceFold ⁻¹' U)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x.1, x.2.val), ?_, halfSpaceDouble_inclusion f x⟩
    simpa only [mem_preimage, halfSpaceFold_inclusion] using hx
  · rintro ⟨x, hx, hxy⟩
    refine ⟨halfSpaceFold x, hx, ?_⟩
    simpa only [halfSpaceFold_double, halfSpaceFold_inclusion] using
      congrArg halfSpaceFold hxy

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem continuous_halfSpaceFold : Continuous (halfSpaceFold : E × ℝ → E × Ici (0 : ℝ)) :=
  continuous_fst.prodMk (continuous_snd.abs.subtype_mk fun p => abs_nonneg p.2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem continuousOn_halfSpaceDouble
    {U : Set (E × Ici (0 : ℝ))}
    {f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)}
    (hf : ContinuousOn f U)
    (hboundary : ∀ x ∈ U, (f x).2.val = 0 ↔ x.2.val = 0) :
    ContinuousOn (halfSpaceDouble f) (halfSpaceFold ⁻¹' U) := by
  have hfold : ContinuousOn (fun p : E × ℝ => f (halfSpaceFold p)) (halfSpaceFold ⁻¹' U) :=
    hf.comp continuous_halfSpaceFold.continuousOn (fun _ hx => hx)
  have hheight : ContinuousOn (fun p : E × ℝ => (f (halfSpaceFold p)).2.val)
      (halfSpaceFold ⁻¹' U) :=
    continuous_subtype_val.comp_continuousOn hfold.snd
  apply hfold.fst.prodMk
  refine ContinuousOn.if ?_ (hheight.mono inter_subset_left) (hheight.neg.mono inter_subset_left)
  rintro p ⟨hp, hfront⟩
  have hpzero : p.2 = 0 := by
    have h := continuous_snd.frontier_preimage_subset (Ici (0 : ℝ)) hfront
    simpa only [mem_preimage, frontier_Ici, mem_singleton_iff] using h
  have hzero : (f (halfSpaceFold p)).2.val = 0 :=
    (hboundary _ hp).mpr (by change |p.2| = 0; rw [hpzero, abs_zero])
  rw [hzero, neg_zero]

theorem isOpen_image_halfSpace_of_continuousOn_injOn_boundary_iff
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {U : Set (E × Ici (0 : ℝ))} (hU : IsOpen U)
    {f : E × Ici (0 : ℝ) → F × Ici (0 : ℝ)}
    (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hboundary : ∀ x ∈ U, (f x).2.val = 0 ↔ x.2.val = 0) :
    IsOpen (f '' U) := by
  have hdim' : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ (F × ℝ) := by
    simp only [Module.finrank_prod, hdim]
  have hopen := invariance_of_domain_isOpen_image_of_finrank_eq hdim'
    (hU.preimage continuous_halfSpaceFold) (continuousOn_halfSpaceDouble hf hboundary)
    (halfSpaceDouble_injOn hinj hboundary)
  rw [image_eq_preimage_halfSpaceDouble]
  exact hopen.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

end DifferentialGeometry.Topology
