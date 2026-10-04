import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevel
import DifferentialGeometry.Topology.Ehresmann.BoundaryInterval
import DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteInteriorPatch
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SmoothDiffeomorph

/-!
# A regular sublevel of a manifold with boundary is a product over its bottom boundary (F-e, E6)

Let `M` be a compact manifold with boundary (model `𝓡∂ (m + 1)`), `f : M → ℝ` smooth with no
critical point on `{f ≤ r}`, and suppose that `f = a < r` on every boundary point of `M` in
`{f ≤ r}`. Then the sublevel `{f ≤ r}`, with the manifold-with-boundary structure of lane SUB-BDY
(`boundarySublevelChartedSpace`, boundary `(∂M ∩ {f ≤ r}) ∪ {f = r}`), is diffeomorphic to
`(bottom boundary) × [a, r]`, by a diffeomorphism carrying the second coordinate to `f` and equal
to the inclusion on the bottom boundary.

This is the kernel of row E6 (BCP01.c: the closed inner collar is `T² × [0, 1]` as a pair): the
bottom boundary is `∂M ∩ {f = a}` (`exists_mem_boundarySublevelBottom_iff`).

* `boundarySublevel_isInteriorPoint_of_eq`, `boundarySublevel_eq_or_eq_of_isBoundaryPoint`: the
  hypotheses of SUB-BDY and of `Ehresmann.exists_boundary_interval_trivialization`, derived;
* `exists_boundarySublevel_interval_trivialization`: the product;
* `exists_mem_boundarySublevelBottom_iff`: the bottom boundary, as a subset of `M`;
* `exists_boundarySublevel_diffeomorph_of_boundary_param`: when the bottom boundary is the image
  of an injective `C^k` immersion `j : T → M` of a compact boundaryless `T` (`1 ≤ k`), the sublevel
  is diffeomorphic to `T × [a, r]` as a pair: `T × {a}` goes onto `range j`. The bottom boundary is
  identified with `T` by the finite-order inverse function theorem (X87) and W-1's upgrade.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Boundary

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]

/-- A level `f = r` avoids the boundary when `f = a ≠ r` on the boundary part of `{f ≤ r}`. -/
theorem boundarySublevel_isInteriorPoint_of_eq {f : M → ℝ} {a r : ℝ} (har : a < r)
    (hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → f x = a) :
    ∀ x : M, f x = r → (𝓡∂ (m + 1)).IsInteriorPoint x := by
  intro x hx
  rw [(𝓡∂ (m + 1)).isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have h := hbd x hb hx.le
  rw [hx] at h
  exact har.ne' h

variable [IsManifold (𝓡∂ (m + 1)) ∞ M]

/-- On the sublevel, boundary points sit at the two levels `a` and `r`. -/
theorem boundarySublevel_eq_or_eq_of_isBoundaryPoint {f : M → ℝ} {a r : ℝ} (har : a < r)
    (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → f x = a) :
    letI := boundarySublevelChartedSpace f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har hbd)
    ∀ y : {x : M // f x ≤ r}, (𝓡∂ (m + 1)).IsBoundaryPoint y → f y.1 = a ∨ f y.1 = r := by
  intro y hy
  rcases (boundarySublevel_isBoundaryPoint_iff hf (fun x hx => hreg x hx.le)
    (boundarySublevel_isInteriorPoint_of_eq har hbd)).mp hy with h | h
  · exact Or.inl (hbd y.1 h y.2)
  · exact Or.inr h

/-- **E6 kernel.** A compact regular sublevel `{f ≤ r}` whose boundary part inside `∂M` lies at
the level `a < r` is diffeomorphic to its bottom boundary times `[a, r]`, carrying the second
coordinate to `f` and restricting to the inclusion at height `a`. -/
theorem exists_boundarySublevel_interval_trivialization [T2Space M] [CompactSpace M]
    {f : M → ℝ} {a r : ℝ} (har : a < r) (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → f x = a)
    (ha : ∃ x, f x = a) (hr : ∃ x, f x = r) :
    letI := boundarySublevelChartedSpace f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har hbd)
    haveI := boundarySublevel_isManifold f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har hbd)
    haveI : Fact (a < r) := ⟨har⟩
    ∃ Θ : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))).prod (𝓡∂ 1))
        (𝓡∂ (m + 1))
        (boundaryLevel (fun y : {x : M // f x ≤ r} => f y.1) a r har.ne
          (hf.continuous.comp continuous_subtype_val)
          (boundarySublevel_eq_or_eq_of_isBoundaryPoint har hf hreg hbd) × Icc a r)
        {x : M // f x ≤ r} ∞,
      (∀ p, f (Θ p).1 = p.2.1) ∧ ∀ y, Θ (y, ⟨a, le_rfl, har.le⟩) = y.1.1 := by
  have hreg' : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hreg x hx.le
  have hint := boundarySublevel_isInteriorPoint_of_eq har hbd
  let _ := boundarySublevelChartedSpace f r hf hreg' hint
  have : Fact (a < r) := ⟨har⟩
  have := boundarySublevel_isManifold f r hf hreg' hint
  have : CompactSpace {x : M // f x ≤ r} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  have hval := boundarySublevel_contMDiff_val f r hf hreg' hint
  have hu : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ (fun y : {x : M // f x ≤ r} => f y.1) :=
    hf.comp hval
  have hureg : ∀ y : {x : M // f x ≤ r},
      mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) (fun y : {x : M // f x ≤ r} => f y.1) y ≠ 0 := by
    intro y h0
    apply hreg y.1 y.2
    have hchain : mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) (fun y : {x : M // f x ≤ r} => f y.1) y =
        (mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f y.1).comp
          (mfderiv (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) (fun y : {x : M // f x ≤ r} => y.1) y) :=
      mfderiv_comp y ((hf y.1).mdifferentiableAt (by simp))
        ((hval y).mdifferentiableAt (by simp))
    rw [hchain] at h0
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := (boundarySublevel_mfderiv_val_bijective f r hf hreg' hint y).2 w
    exact DFunLike.congr_fun h0 v
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xr, hxr⟩ := hr
  have ha' : a ∈ range (fun y : {x : M // f x ≤ r} => f y.1) :=
    ⟨⟨xa, hxa.le.trans har.le⟩, hxa⟩
  have hr' : r ∈ range (fun y : {x : M // f x ≤ r} => f y.1) := ⟨⟨xr, hxr.le⟩, hxr⟩
  exact Ehresmann.exists_boundary_interval_trivialization har hu hureg
    (boundarySublevel_eq_or_eq_of_isBoundaryPoint har hf hreg hbd) ha' hr'

/-- The bottom boundary of the sublevel, as a subset of `M`, is `∂M ∩ {f = a}`. -/
theorem exists_mem_boundarySublevelBottom_iff {f : M → ℝ} {a r : ℝ} (har : a < r)
    (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → f x = a) {x : M} :
    letI := boundarySublevelChartedSpace f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har hbd)
    haveI := boundarySublevel_isManifold f r hf (fun x hx => hreg x hx.le)
      (boundarySublevel_isInteriorPoint_of_eq har hbd)
    (∃ y : boundaryLevel (fun y : {x : M // f x ≤ r} => f y.1) a r har.ne
        (hf.continuous.comp continuous_subtype_val)
        (boundarySublevel_eq_or_eq_of_isBoundaryPoint har hf hreg hbd), y.1.1.1 = x) ↔
      ((𝓡∂ (m + 1)).IsBoundaryPoint x ∧ f x = a) := by
  have hreg' : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hreg x hx.le
  have hint := boundarySublevel_isInteriorPoint_of_eq har hbd
  let _ := boundarySublevelChartedSpace f r hf hreg' hint
  constructor
  · rintro ⟨y, rfl⟩
    have hya : f y.1.1.1 = a := y.2
    refine ⟨?_, hya⟩
    rcases (boundarySublevel_isBoundaryPoint_iff hf hreg' hint).mp y.1.2 with h | h
    · exact h
    · exact absurd (hya.symm.trans h) har.ne
  · rintro ⟨hb, hfa⟩
    have hle : f x ≤ r := hfa.le.trans har.le
    have hyb : (𝓡∂ (m + 1)).IsBoundaryPoint (⟨x, hle⟩ : {x : M // f x ≤ r}) :=
      (boundarySublevel_isBoundaryPoint_iff hf hreg' hint).mpr (Or.inl hb)
    exact ⟨⟨⟨⟨x, hle⟩, hyb⟩, hfa⟩, rfl⟩

omit [IsManifold (𝓡∂ (m + 1)) ∞ M] in
private theorem contMDiff_opens_iff {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace H'' Y] {U : TopologicalSpace.Opens Y} {n : ℕ∞ω} {g : X → U} :
    ContMDiff I' I'' n (Subtype.val ∘ g) ↔ ContMDiff I' I'' n g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) g univ x

variable {F G T : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace T] [ChartedSpace G T] [IsManifold J ∞ T]

/-- **E6 kernel, pair form.** If the boundary part of a compact regular sublevel `{f ≤ r}` is the
image of an injective `C^k` immersion `j` of a compact boundaryless `T` on which `f = a < r`, then
the sublevel is diffeomorphic to `T × [a, r]`, carrying the second coordinate to `f`; `T × {a}`
goes onto `range j`. -/
theorem exists_boundarySublevel_diffeomorph_of_boundary_param [T2Space M] [CompactSpace M]
    [Nonempty T] [CompactSpace T] [T2Space T] (hdim : Module.finrank ℝ F = m)
    {f : M → ℝ} {a r : ℝ} (har : a < r) (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x ≤ r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (hr : ∃ x, f x = r)
    {k : ℕ} (hk : 1 ≤ k) {j : T → M} (hj : ContMDiff J (𝓡∂ (m + 1)) k j)
    (hjinj : Injective j) (hjd : ∀ t, Injective (mfderiv J (𝓡∂ (m + 1)) j t))
    (hjbd : ∀ t, (𝓡∂ (m + 1)).IsBoundaryPoint (j t)) (hja : ∀ t, f (j t) = a)
    (hjrange : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → f x ≤ r → x ∈ range j) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) {x : M // f x ≤ r},
      letI := cs
      IsManifold (𝓡∂ (m + 1)) ∞ {x : M // f x ≤ r} ∧
      ContMDiff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) ∞ (fun x : {x : M // f x ≤ r} => x.1) ∧
      (∀ y : {x : M // f x ≤ r},
        (𝓡∂ (m + 1)).IsBoundaryPoint y ↔ (y.1 ∈ range j ∨ f y.1 = r)) ∧
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
    rw [← contMDiff_opens_iff (U := L)]
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
  refine ⟨_, inferInstance, hval, fun y => ?_, D, hDf, fun p => ?_⟩
  · rw [boundarySublevel_isBoundaryPoint_iff hf hreg' hint]
    constructor
    · rintro (h | h)
      · exact Or.inl (hjrange _ h y.2)
      · exact Or.inr h
    · rintro (⟨t, ht⟩ | h)
      · exact Or.inl (ht ▸ hjbd t)
      · exact Or.inr h
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

end DifferentialGeometry.Topology.Manifold
