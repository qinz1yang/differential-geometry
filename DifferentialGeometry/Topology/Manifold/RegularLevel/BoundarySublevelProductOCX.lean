import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevelProduct
import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceImmersionBdryOCX

/-!
# E6 kernel with the CONCRETE sublevel structure, and the product as a smooth embedding

Lane O-CROSS (G2). `exists_boundarySublevel_diffeomorph_of_boundary_param` (lane E6) hides the
charted space of the sublevel `{f ≤ r}` behind an `∃ cs`; the rows need the product as a smooth
embedding into `M`, which uses the charts of lane SUB-BDY's `boundarySublevelChartedSpace`
(`boundarySublevel_isSmoothEmbedding_val_OCX`). This file restates the E6 kernel for that charted
space (same proof) and composes:

* `exists_boundarySublevel_diffeomorph_of_boundary_param_OCX`: the product diffeomorphism
  `T × [a, r] ≅ {f ≤ r}` for `boundarySublevelChartedSpace`;
* `exists_boundarySublevel_embedding_of_boundary_param_OCX`: given a linear `Λ : F × ℝ¹ ≃ ℝ^{m+2}`
  matching `range (J.prod (𝓡∂ 1))` with the half-space, a smooth embedding
  `Φ : T × [a, r] → M` onto `{f ≤ r}` with `f ∘ Φ = pr₂` and `T × {a}` onto `range j`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Boundary

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
  [IsManifold (𝓡∂ (m + 1)) ∞ M]

omit [IsManifold (𝓡∂ (m + 1)) ∞ M] in
private theorem contMDiff_opens_iff_OCX {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace H'' Y] {U : TopologicalSpace.Opens Y} {n : ℕ∞ω} {g : X → U} :
    ContMDiff I' I'' n (Subtype.val ∘ g) ↔ ContMDiff I' I'' n g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) g univ x

variable {F G T : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace T] [ChartedSpace G T] [IsManifold J ∞ T]

/-- **E6 kernel, pair form, for the concrete sublevel structure** (`boundarySublevelChartedSpace`;
same proof as `exists_boundarySublevel_diffeomorph_of_boundary_param`). -/
theorem exists_boundarySublevel_diffeomorph_of_boundary_param_OCX [T2Space M] [CompactSpace M]
    [Nonempty T] [CompactSpace T] [T2Space T] (hdim : Module.finrank ℝ F = m)
    {f : M → ℝ} {a r : ℝ} (har : a < r) (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (hr : ∃ x, f x = r)
    {k : ℕ} (hk : 1 ≤ k) {j : T → M} (hj : ContMDiff J (𝓡∂ (m + 1)) k j)
    (hjinj : Injective j) (hjd : ∀ t, Injective (mfderiv J (𝓡∂ (m + 1)) j t))
    (hjbd : ∀ t, (𝓡∂ (m + 1)).IsBoundaryPoint (j t)) (hja : ∀ t, f (j t) = a)
    (hjrange : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → x ∈ range j) :
    letI := boundarySublevelChartedSpace f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har (fun x hx hxr => by
        obtain ⟨t, ht⟩ := hjrange x hx hxr
        rw [← ht]
        exact hja t))
    haveI : Fact (a < r) := ⟨har⟩
    ∃ D : Diffeomorph (J.prod (𝓡∂ 1)) (𝓡∂ (m + 1)) (T × Icc a r) {x : M // f x ≤ r} ∞,
      (∀ p, f (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ range j ↔ p.2.1 = a := by
  classical
  have hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → f x = a := by
    intro x hx hxr
    obtain ⟨t, rfl⟩ := hjrange x hx hxr
    exact hja t
  have hreg' : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hreg x hx.le
  have hint := boundarySublevel_isInteriorPoint_of_eq har hbd
  let _ := boundarySublevelChartedSpace f r hf hreg' hint
  have _ := boundarySublevel_isManifold f r hf hreg' hint
  have : Fact (a < r) := ⟨har⟩
  have hval := boundarySublevel_contMDiff_val f r hf hreg' hint
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨Θ, hΘf, hΘa⟩ := exists_boundarySublevel_interval_trivialization har hf hreg hbd
    ⟨j t₀, hja t₀⟩ hr
  let L := boundaryLevel (fun y : {x : M // f x ≤ r} => f y.1) a r har.ne
    (hf.continuous.comp continuous_subtype_val)
    (boundarySublevel_eq_or_eq_of_isBoundaryPoint har hf hreg hbd)
  have hmemL := fun x : M => exists_mem_boundarySublevelBottom_iff har hf hreg hbd (x := x)
  -- the parametrisation of the bottom boundary
  have hjS : ∀ t, f (j t) ≤ r := fun t => (hja t).le.trans har.le
  have hjSb : ∀ t, (𝓡∂ (m + 1)).IsBoundaryPoint (⟨j t, hjS t⟩ : {x : M // f x ≤ r}) :=
    fun t => (boundarySublevel_isBoundaryPoint_iff hf hreg' hint).mpr (Or.inl (hjbd t))
  let φ : T → L := fun t => ⟨⟨⟨j t, hjS t⟩, hjSb t⟩, hja t⟩
  have hφj : ∀ t, (φ t).1.1.1 = j t := fun _ => rfl
  let ιL : L → M := fun y => y.1.1.1
  have hιL : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞ ιL :=
    hval.comp ((contMDiff_boundaryLevelInclusion _ a r har.ne _ _))
  have hφ : ContMDiff J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) k φ := by
    rw [← contMDiff_opens_iff_OCX (U := L)]
    rw [DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff
      (by exact_mod_cast le_top)]
    have h := (boundarySublevel_contMDiff_iff hf hreg' hint (n := (k : ℕ∞))
      (J := J) (g := fun t => ((φ t).1 : {x : M // f x ≤ r}))).mpr (by exact_mod_cast hj)
    exact_mod_cast h
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hφd : ∀ t, Injective
      (mfderiv J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) φ t) := by
    intro t v w hvw
    apply hjd t
    have hcomp : mfderiv J (𝓡∂ (m + 1)) (ιL ∘ φ) t =
        (mfderiv (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ιL (φ t)).comp
          (mfderiv J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) φ t) :=
      mfderiv_comp t ((hιL (φ t)).mdifferentiableAt (by simp))
        ((hφ t).mdifferentiableAt hk0)
    have hιφ : ιL ∘ φ = j := rfl
    rw [hιφ] at hcomp
    rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvw]
  have hdimL : Module.finrank ℝ F =
      Module.finrank ℝ (HasSmoothBoundary.boundaryModelE (𝓡∂ (m + 1))) := by
    change Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1 - 1)))
    rw [finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel, hdim]
  have hφloc : IsLocalDiffeomorph J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) k φ := by
    intro t
    obtain ⟨Ψ, htΨ, -, hφΨ, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_finiteInteriorPatch hk isOpen_univ
        hφ.contMDiffOn (mem_univ t) BoundarylessManifold.isInteriorPoint
        BoundarylessManifold.isInteriorPoint hdimL (hφd t)
    exact ⟨Ψ, htΨ, hφΨ⟩
  have hφbij : Bijective φ := by
    refine ⟨fun t₁ t₂ h => hjinj (congrArg (fun y : L => y.1.1.1) h), fun y => ?_⟩
    obtain ⟨hyb, hya⟩ := (hmemL y.1.1.1).mp ⟨y, rfl⟩
    obtain ⟨t, ht⟩ := hjrange _ hyb (hya.le.trans har.le)
    exact ⟨t, Subtype.ext (Subtype.ext (Subtype.ext ht))⟩
  let d : T ≃ₘ^k⟮J, HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))⟯ L :=
    hφloc.diffeomorphOfBijective hφbij
  obtain ⟨d'⟩ := SmoothApproximation.nonempty_diffeomorph_of_diffeomorph k hk d
  let D := (d'.prodCongr (Diffeomorph.refl (𝓡∂ 1) (Icc a r) ∞)).trans Θ
  have hDf : ∀ p, f (D p).1 = p.2.1 := fun p => hΘf (d' p.1, p.2)
  refine ⟨D, hDf, fun p => ?_⟩
  · constructor
    · rintro ⟨t, ht⟩
      rw [← hDf p, ← ht]
      exact hja t
    · intro hp
      have hp2 : p.2 = ⟨a, le_rfl, har.le⟩ := Subtype.ext hp
      have hDp : D p = Θ (d' p.1, ⟨a, le_rfl, har.le⟩) := by
        change Θ (d' p.1, p.2) = _
        rw [hp2]
      rw [hDp, hΘa]
      obtain ⟨hyb, hya⟩ := (hmemL (d' p.1).1.1.1).mp ⟨d' p.1, rfl⟩
      exact hjrange _ hyb (hya.le.trans har.le)


section Embedding

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1 + 1)) M] [IsManifold (𝓡∂ (m + 1 + 1)) ∞ M]
  {F G T : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace T] [ChartedSpace G T] [IsManifold J ∞ T]

/-- **E6 kernel as a smooth embedding**: the product `T × [a, r] ≅ {f ≤ r}` followed by the
inclusion is a smooth embedding into `M` (model change by a linear `Λ` matching
`range (J.prod (𝓡∂ 1))` with the half-space), onto `{f ≤ r}`, with `f ∘ Φ = pr₂` and
`T × {a}` onto `range j`. -/
theorem exists_boundarySublevel_embedding_of_boundary_param_OCX [T2Space M] [CompactSpace M]
    [Nonempty T] [CompactSpace T] [T2Space T] (hdim : Module.finrank ℝ F = m + 1)
    (Λ : (F × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1 + 1)))
    (hΛ : ∀ v, Λ v + 0 ∈ range (𝓡∂ (m + 1 + 1)) ↔ v ∈ range (J.prod (𝓡∂ 1)))
    {f : M → ℝ} {a r : ℝ} (har : a < r) (hf : ContMDiff (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (hr : ∃ x, f x = r)
    {k : ℕ} (hk : 1 ≤ k) {j : T → M} (hj : ContMDiff J (𝓡∂ (m + 1 + 1)) k j)
    (hjinj : Injective j) (hjd : ∀ t, Injective (mfderiv J (𝓡∂ (m + 1 + 1)) j t))
    (hjbd : ∀ t, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint (j t)) (hja : ∀ t, f (j t) = a)
    (hjrange : ∀ x, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint x → f x ≤ r → x ∈ range j) :
    haveI : Fact (a < r) := ⟨har⟩
    ∃ Φ : T × Icc a r → M, IsSmoothEmbedding (J.prod (𝓡∂ 1)) (𝓡∂ (m + 1 + 1)) ∞ Φ ∧
      range Φ = {x | f x ≤ r} ∧ (∀ p, f (Φ p) = p.2.1) ∧ ∀ p, Φ p ∈ range j ↔ p.2.1 = a := by
  have : Fact (a < r) := ⟨har⟩
  have hbd : ∀ x, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint x → f x ≤ r → f x = a := by
    intro x hx hxr
    obtain ⟨t, ht⟩ := hjrange x hx hxr
    rw [← ht]
    exact hja t
  have hint := boundarySublevel_isInteriorPoint_of_eq har hbd
  let _ := boundarySublevelChartedSpace f r hf (fun x hx => hreg x hx.le) hint
  have _ := boundarySublevel_isManifold f r hf (fun x hx => hreg x hx.le) hint
  obtain ⟨D, hDf, hDj⟩ := exists_boundarySublevel_diffeomorph_of_boundary_param_OCX
    (m := m + 1) hdim har hf hreg hr hk hj hjinj hjd hjbd hja hjrange
  have hval := boundarySublevel_isSmoothEmbedding_val_OCX f r hf (fun x hx => hreg x hx.le) hint
  refine ⟨(fun x : {x : M // f x ≤ r} => x.1) ∘ D, hval.comp_diffeomorph_linear_OCX Λ hΛ D,
    ?_, hDf, hDj⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (D p).2
  · intro hx
    obtain ⟨p, hp⟩ := D.surjective ⟨x, hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩

/-- **E6 kernel, full concrete form**: the sublevel structure of lane SUB-BDY (manifold, smooth
inclusion, boundary `range j ∪ {f = r}`) together with the product diffeomorphism `D` AND the
smooth embedding `val ∘ D` into `M` (model change by `Λ`). -/
theorem exists_boundarySublevel_product_embedding_full_OCX [T2Space M] [CompactSpace M]
    [Nonempty T] [CompactSpace T] [T2Space T] (hdim : Module.finrank ℝ F = m + 1)
    (Λ : (F × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1 + 1)))
    (hΛ : ∀ v, Λ v + 0 ∈ range (𝓡∂ (m + 1 + 1)) ↔ v ∈ range (J.prod (𝓡∂ 1)))
    {f : M → ℝ} {a r : ℝ} (har : a < r) (hf : ContMDiff (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (hr : ∃ x, f x = r)
    {k : ℕ} (hk : 1 ≤ k) {j : T → M} (hj : ContMDiff J (𝓡∂ (m + 1 + 1)) k j)
    (hjinj : Injective j) (hjd : ∀ t, Injective (mfderiv J (𝓡∂ (m + 1 + 1)) j t))
    (hjbd : ∀ t, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint (j t)) (hja : ∀ t, f (j t) = a)
    (hjrange : ∀ x, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint x → f x ≤ r → x ∈ range j) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1 + 1)) {x : M // f x ≤ r},
      letI := cs
      IsManifold (𝓡∂ (m + 1 + 1)) ∞ {x : M // f x ≤ r} ∧
      ContMDiff (𝓡∂ (m + 1 + 1)) (𝓡∂ (m + 1 + 1)) ∞ (fun x : {x : M // f x ≤ r} => x.1) ∧
      (∀ y : {x : M // f x ≤ r},
        (𝓡∂ (m + 1 + 1)).IsBoundaryPoint y ↔ (y.1 ∈ range j ∨ f y.1 = r)) ∧
      haveI : Fact (a < r) := ⟨har⟩
      ∃ D : Diffeomorph (J.prod (𝓡∂ 1)) (𝓡∂ (m + 1 + 1)) (T × Icc a r) {x : M // f x ≤ r} ∞,
        (∀ p, f (D p).1 = p.2.1) ∧ (∀ p, (D p).1 ∈ range j ↔ p.2.1 = a) ∧
        IsSmoothEmbedding (J.prod (𝓡∂ 1)) (𝓡∂ (m + 1 + 1)) ∞ (fun p => (D p).1) := by
  have : Fact (a < r) := ⟨har⟩
  have hbd : ∀ x, (𝓡∂ (m + 1 + 1)).IsBoundaryPoint x → f x ≤ r → f x = a := by
    intro x hx hxr
    obtain ⟨t, ht⟩ := hjrange x hx hxr
    rw [← ht]
    exact hja t
  have hreg' : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hreg x hx.le
  have hint := boundarySublevel_isInteriorPoint_of_eq har hbd
  let _ := boundarySublevelChartedSpace f r hf hreg' hint
  have _ := boundarySublevel_isManifold f r hf hreg' hint
  obtain ⟨D, hDf, hDj⟩ := exists_boundarySublevel_diffeomorph_of_boundary_param_OCX
    (m := m + 1) hdim har hf hreg hr hk hj hjinj hjd hjbd hja hjrange
  have hval := boundarySublevel_isSmoothEmbedding_val_OCX f r hf hreg' hint
  refine ⟨_, inferInstance, boundarySublevel_contMDiff_val f r hf hreg' hint, fun y => ?_, D, hDf,
    hDj, hval.comp_diffeomorph_linear_OCX Λ hΛ D⟩
  rw [boundarySublevel_isBoundaryPoint_iff hf hreg' hint]
  constructor
  · rintro (h | h)
    · exact Or.inl (hjrange _ h y.2)
    · exact Or.inr h
  · rintro (⟨t, ht⟩ | h)
    · exact Or.inl (ht ▸ hjbd t)
    · exact Or.inr h

end Embedding

end DifferentialGeometry.Topology.Manifold
