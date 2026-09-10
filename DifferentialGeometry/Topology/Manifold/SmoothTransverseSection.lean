/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.SmoothNormalReorientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

open Bundle Filter Manifold Set Topology
open scoped Bundle Manifold ContDiff

noncomputable section

universe u v w x y z

namespace DifferentialGeometry.Topology

namespace OpenPartialHomeomorph

set_option backward.isDefEq.respectTransparency false in
theorem normalDeriv_eq_snd_mfderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {B : Type w} [TopologicalSpace B] [ChartedSpace H B]
    {I : ModelWithCorners ℝ E H}
    (e : OpenPartialHomeomorph (B × ℝ) (B × ℝ)) {x : B}
    (he : MDifferentiableAt (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) e (x, 0)) :
    normalDeriv e x =
      (mfderiv (I.prod (modelWithCornersSelf ℝ ℝ))
        (I.prod (modelWithCornersSelf ℝ ℝ)) e (x, 0) (0, 1)).2 := by
  let oneT : TangentSpace (modelWithCornersSelf ℝ ℝ) (0 : ℝ) := by
    change ℝ
    exact 1
  let normalT : TangentSpace (I.prod (modelWithCornersSelf ℝ ℝ)) (x, (0 : ℝ)) := by
    change E × ℝ
    exact (0, 1)
  let c : ℝ → B × ℝ := fun t ↦ (x, t)
  have hcDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (I.prod (modelWithCornersSelf ℝ ℝ)) c 0 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hecDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (I.prod (modelWithCornersSelf ℝ ℝ)) (fun t : ℝ ↦ e (x, t)) 0 :=
    he.comp 0 hcDiff
  have hsndDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) (fun t : ℝ ↦ (e (x, t)).2) 0 :=
    mdifferentiableAt_snd.comp 0 hecDiff
  have hcurveDeriv :
      mfderiv (modelWithCornersSelf ℝ ℝ) (I.prod (modelWithCornersSelf ℝ ℝ)) c 0 =
        ContinuousLinearMap.inr ℝ E ℝ := by
    exact mfderiv_prod_right
  have hcurveDerivOne :
      mfderiv (modelWithCornersSelf ℝ ℝ) (I.prod (modelWithCornersSelf ℝ ℝ)) c 0 oneT =
        normalT := by
    rw [hcurveDeriv]
    rfl
  change deriv (fun t : ℝ ↦ (e (x, t)).2) 0 = _
  calc
    deriv (fun t : ℝ ↦ (e (x, t)).2) 0 =
        NormedSpace.fromTangentSpace ((e (x, 0)).2)
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
            (fun t : ℝ ↦ (e (x, t)).2) 0 oneT) := by
              rw [mfderiv_eq_fderiv]
              rfl
    _ = (mfderiv (modelWithCornersSelf ℝ ℝ) (I.prod (modelWithCornersSelf ℝ ℝ))
          (fun t : ℝ ↦ e (x, t)) 0 oneT).2 := by
            have hcomp := mfderiv_comp_apply 0 mdifferentiableAt_snd hecDiff oneT
            rw [mfderiv_snd] at hcomp
            exact congrArg (NormedSpace.fromTangentSpace ((e (x, 0)).2)) hcomp
    _ = (mfderiv (I.prod (modelWithCornersSelf ℝ ℝ))
          (I.prod (modelWithCornersSelf ℝ ℝ)) e (x, 0)
            (mfderiv (modelWithCornersSelf ℝ ℝ)
              (I.prod (modelWithCornersSelf ℝ ℝ)) c 0 oneT)).2 := by
            congr 1
            simpa [c, Function.comp_def] using
              (mfderiv_comp_apply 0 he hcDiff oneT)
    _ = _ := by rw [hcurveDerivOne]; rfl

end OpenPartialHomeomorph

namespace SmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {f : B → A}

theorem contMDiff (C : SmoothEmbeddingRealNormalAtlas I J n f) : ContMDiff I J n f := by
  intro x
  let R := SmoothEmbeddingRealNormalAtlas.toEmbeddingRealNormalAtlas C
  let z : B → B × ℝ := fun y ↦ (y, 0)
  have hz : ContMDiff I (I.prod (modelWithCornersSelf ℝ ℝ)) n z :=
    contMDiff_id.prodMk contMDiff_const
  have hlocal : ContMDiffOn I J n (fun y ↦ R.chart x (z y)) (R.baseSet x) :=
    (C.contMDiffOn_chart x).comp hz.contMDiffOn
      (fun y hy ↦ R.zero_mem_source x hy)
  have heq : (fun y ↦ R.chart x (z y)) =ᶠ[nhds x] f := by
    apply eventually_of_mem ((R.isOpen_baseSet x).mem_nhds (R.mem_baseSet_self x))
    intro y hy
    exact R.apply_zero x hy
  exact (hlocal.contMDiffAt
    ((R.isOpen_baseSet x).mem_nhds (R.mem_baseSet_self x))).congr_of_eventuallyEq heq.symm

noncomputable def continuousMap (C : SmoothEmbeddingRealNormalAtlas I J n f) : C(B, A) :=
  ⟨f, C.contMDiff.continuous⟩

end SmoothEmbeddingRealNormalAtlas

namespace CoorientedSmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {m : ℕ∞} {f : B → A}
    (C : CoorientedSmoothEmbeddingRealNormalAtlas I J n f)

abbrev normalAtlas : EmbeddingRealNormalAtlas f :=
  SmoothEmbeddingRealNormalAtlas.toEmbeddingRealNormalAtlas
    (CoorientedSmoothEmbeddingRealNormalAtlas.toSmoothEmbeddingRealNormalAtlas C)

noncomputable def continuousMap : C(B, A) :=
  SmoothEmbeddingRealNormalAtlas.continuousMap
    (CoorientedSmoothEmbeddingRealNormalAtlas.toSmoothEmbeddingRealNormalAtlas C)

noncomputable def localNormal (i y : B) : TangentSpace J (f y) :=
  mfderiv (I.prod (modelWithCornersSelf ℝ ℝ)) J (C.normalAtlas.chart i) (y, 0) (0, 1)

noncomputable def positiveNormalFunctional (x : B) : TangentSpace J (f x) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ E ℝ).comp
    (mfderiv J (I.prod (modelWithCornersSelf ℝ ℝ))
      (C.normalAtlas.chart x).symm (f x))

def positiveNormalHalfSpace (x : B) : Set (TangentSpace J (f x)) :=
  C.positiveNormalFunctional x ⁻¹' Ioi 0

theorem convex_positiveNormalHalfSpace (x : B) :
    Convex ℝ (C.positiveNormalHalfSpace x) :=
  (convex_Ioi 0).linear_preimage (C.positiveNormalFunctional x).toLinearMap

set_option backward.isDefEq.respectTransparency false in
private theorem contMDiff_normalInput [IsManifold I 1 B] :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ ℝ)).tangent (m : ℕ∞ω)
      (fun y : B ↦
        (⟨(y, (0 : ℝ)), (0, 1)⟩ :
          TangentBundle (I.prod (modelWithCornersSelf ℝ ℝ)) (B × ℝ))) := by
  let oneT : TangentSpace (modelWithCornersSelf ℝ ℝ) (0 : ℝ) := by
    change ℝ
    exact 1
  let q : B → (TangentBundle I B) ×
      (TangentBundle (modelWithCornersSelf ℝ ℝ) ℝ) :=
    fun y ↦ (⟨y, 0⟩, ⟨0, oneT⟩)
  have hzero : ContMDiff I I.tangent (m : ℕ∞ω)
      (Bundle.zeroSection E (TangentSpace I : B → Type _)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace I)
  have hq : ContMDiff I
      (I.tangent.prod (modelWithCornersSelf ℝ ℝ).tangent) (m : ℕ∞ω) q :=
    hzero.prodMk contMDiff_const
  have hequiv := contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := modelWithCornersSelf ℝ ℝ) (M := B) (M' := ℝ) (n := (m : ℕ∞ω))
  exact (hequiv.comp hq).congr fun y ↦ rfl

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_localNormal
    [IsManifold I ∞ B] [IsManifold J ∞ A]
    (hmn : (m : ℕ∞ω) + 1 ≤ n) (i : B) :
    ContMDiffOn I (I.prod (modelWithCornersSelf ℝ F)) (m : ℕ∞ω)
      (fun y ↦ (⟨y, C.localNormal i y⟩ :
        TotalSpace F (C.continuousMap *ᵖ (TangentSpace J : A → Type _))))
      (C.normalAtlas.baseSet i) := by
  let R := C.normalAtlas
  let S := CoorientedSmoothEmbeddingRealNormalAtlas.toSmoothEmbeddingRealNormalAtlas C
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  let fMap : C^(m : ℕ∞ω)⟮I, B; J, A⟯ :=
    ⟨C.continuousMap, by
      simpa [continuousMap, SmoothEmbeddingRealNormalAtlas.continuousMap] using
        S.contMDiff.of_le (le_self_add.trans hmn)⟩
  let hTangent : ContMDiffVectorBundle (m : ℕ∞ω) F
      (TangentSpace J : A → Type _) J := inferInstance
  let : ContMDiffVectorBundle (m : ℕ∞ω) F
      (C.continuousMap *ᵖ (TangentSpace J : A → Type _)) I :=
    ContMDiffVectorBundle.pullback (F := F) (E := (TangentSpace J : A → Type _)) I fMap
  let q : B → TangentBundle IP (B × ℝ) :=
    fun y ↦ ⟨(y, 0), (0, 1)⟩
  let t : B → TangentBundle J A :=
    fun y ↦ tangentMapWithin IP J (R.chart i) (R.chart i).source (q y)
  have htangent : ContMDiffOn IP.tangent J.tangent (m : ℕ∞ω)
      (tangentMapWithin IP J (R.chart i) (R.chart i).source)
      (π (E × ℝ) (TangentSpace IP) ⁻¹' (R.chart i).source) :=
    (S.contMDiffOn_chart i).contMDiffOn_tangentMapWithin hmn
      (R.chart i).open_source.uniqueMDiffOn
  have hq : ContMDiff I IP.tangent (m : ℕ∞ω) q :=
    contMDiff_normalInput (I := I) (m := m)
  have ht : ContMDiffOn I J.tangent (m : ℕ∞ω) t (R.baseSet i) :=
    htangent.comp hq.contMDiffOn fun y hy ↦ R.zero_mem_source i hy
  intro y₀ hy₀
  let e := trivializationAt F (TangentSpace J) (f y₀)
  let ep := e.pullback C.continuousMap
  let : MemTrivializationAtlas ep := ⟨by
    exact ⟨e, inferInstance, rfl⟩⟩
  have hy₀e : y₀ ∈ ep.baseSet := by
    change f y₀ ∈ e.baseSet
    exact mem_baseSet_trivializationAt F (TangentSpace J) (f y₀)
  rw [ep.contMDiffWithinAt_section (R.baseSet i) hy₀e]
  have ht₀ : t y₀ = ⟨f y₀, C.localNormal i y₀⟩ := by
    refine TotalSpace.ext (R.apply_zero i hy₀) ?_
    apply heq_of_eq
    change mfderivWithin IP J (R.chart i) (R.chart i).source (y₀, 0) (0, 1) =
      mfderiv IP J (R.chart i) (y₀, 0) (0, 1)
    rw [mfderivWithin_of_mem_nhds]
    exact (R.chart i).open_source.mem_nhds (R.zero_mem_source i hy₀)
  have ht₀source : t y₀ ∈ e.source := by
    rw [ht₀]
    exact e.mem_source.mpr (mem_baseSet_trivializationAt F (TangentSpace J) (f y₀))
  have heAt : ContMDiffAt J.tangent J.tangent (m : ℕ∞ω) e (t y₀) :=
    (e.contMDiffOn (n := (m : ℕ∞ω))).contMDiffAt (e.open_source.mem_nhds ht₀source)
  have hcoord : ContMDiffWithinAt I (modelWithCornersSelf ℝ F) (m : ℕ∞ω)
      (fun y ↦ (e (t y)).2) (R.baseSet i) y₀ :=
    contMDiffAt_snd.comp_contMDiffWithinAt y₀
      (heAt.comp_contMDiffWithinAt y₀ (ht y₀ hy₀))
  apply hcoord.congr
  · intro y hy
    have hty : t y = ⟨f y, C.localNormal i y⟩ := by
      refine TotalSpace.ext (R.apply_zero i hy) ?_
      apply heq_of_eq
      change mfderivWithin IP J (R.chart i) (R.chart i).source (y, 0) (0, 1) =
        mfderiv IP J (R.chart i) (y, 0) (0, 1)
      rw [mfderivWithin_of_mem_nhds]
      exact (R.chart i).open_source.mem_nhds (R.zero_mem_source i hy)
    simp only [ep, Bundle.Trivialization.pullback_apply]
    rw [hty]
    rfl
  · simp only [ep, Bundle.Trivialization.pullback_apply]
    rw [ht₀]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem localNormal_mem_positiveNormalHalfSpace
    (hn : (1 : ℕ∞ω) ≤ n) {i y : B} (hy : y ∈ C.normalAtlas.baseSet i) :
    C.localNormal i y ∈ C.positiveNormalHalfSpace y := by
  let R := C.normalAtlas
  let S := CoorientedSmoothEmbeddingRealNormalAtlas.toSmoothEmbeddingRealNormalAtlas C
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  let normalT : TangentSpace IP (y, (0 : ℝ)) := by
    change E × ℝ
    exact (0, 1)
  have hySelf : y ∈ R.baseSet y := R.mem_baseSet_self y
  have hsource : (y, 0) ∈ (R.transition i y).source :=
    R.zero_mem_transition_source hy hySelf
  have htransDiff : MDifferentiableAt IP IP (R.transition i y) (y, 0) :=
    (S.isLocalDiffeomorphAt_transition hn hsource).mdifferentiableAt one_ne_zero
  have hchartDiff : MDifferentiableAt IP J (R.chart i) (y, 0) :=
    ((S.contMDiffOn_chart i) (y, 0) (R.zero_mem_source i hy)).mdifferentiableWithinAt
        (lt_of_lt_of_le zero_lt_one hn).ne' |>.mdifferentiableAt
          ((R.chart i).open_source.mem_nhds (R.zero_mem_source i hy))
  have hinvDiff : MDifferentiableAt J IP (R.chart y).symm (f y) := by
    have hfy : f y ∈ (R.chart y).target := by
      rw [← R.apply_zero y hySelf]
      exact (R.chart y).map_source (R.zero_mem_source y hySelf)
    exact ((S.contMDiffOn_chart_symm y) (f y) hfy)
      |>.mdifferentiableWithinAt (lt_of_lt_of_le zero_lt_one hn).ne'
      |>.mdifferentiableAt ((R.chart y).open_target.mem_nhds hfy)
  have happly : R.chart i (y, 0) = f y := R.apply_zero i hy
  have hchain := mfderiv_comp_apply_of_eq (I := IP) (I' := J) (I'' := IP)
    (f := R.chart i) (g := (R.chart y).symm) (x := (y, 0))
      hinvDiff hchartDiff happly normalT
  have hchain' :
      mfderiv IP IP (R.transition i y) (y, 0) normalT =
        mfderiv J IP (R.chart y).symm (f y)
          (mfderiv IP J (R.chart i) (y, 0) normalT) := by
    simpa [EmbeddingRealNormalAtlas.transition, Function.comp_def] using hchain
  have hnormal := OpenPartialHomeomorph.normalDeriv_eq_snd_mfderiv
    (I := I) (R.transition i y) htransDiff
  have hnormal' : OpenPartialHomeomorph.normalDeriv (R.transition i y) y =
      (mfderiv IP IP (R.transition i y) (y, 0) normalT).2 := by
    simpa [normalT] using hnormal
  change 0 < C.positiveNormalFunctional y (C.localNormal i y)
  rw [show C.positiveNormalFunctional y (C.localNormal i y) =
      OpenPartialHomeomorph.normalDeriv (R.transition i y) y by
    rw [hnormal']
    change ((mfderiv J IP (R.chart y).symm (f y))
      ((mfderiv IP J (R.chart i) (y, 0)) normalT)).2 = _
    exact congrArg Prod.snd hchain'.symm]
  exact C.normalDeriv_transition_pos hn hy hySelf

set_option backward.isDefEq.respectTransparency false in
theorem positiveNormalFunctional_mfderiv_eq_zero
    (hn : (1 : ℕ∞ω) ≤ n) (x : B) (v : TangentSpace I x) :
    C.positiveNormalFunctional x (mfderiv I J f x v) = 0 := by
  let R := C.normalAtlas
  let S := CoorientedSmoothEmbeddingRealNormalAtlas.toSmoothEmbeddingRealNormalAtlas C
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  let z : B → B × ℝ := fun y ↦ (y, 0)
  have hx : x ∈ R.baseSet x := R.mem_baseSet_self x
  have hlocal : (fun y ↦ (R.chart x).symm (f y)) =ᶠ[nhds x] z := by
    apply eventually_of_mem ((R.isOpen_baseSet x).mem_nhds hx)
    intro y hy
    change (R.chart x).symm (f y) = (y, 0)
    rw [← R.apply_zero x hy]
    exact (R.chart x).left_inv (R.zero_mem_source x hy)
  have hderivEq :
      mfderiv I IP (fun y ↦ (R.chart x).symm (f y)) x = mfderiv I IP z x :=
    hlocal.mfderiv_eq
  have hfDiff : MDifferentiableAt I J f x :=
    (S.contMDiff.contMDiffAt.mdifferentiableWithinAt
      (lt_of_lt_of_le zero_lt_one hn).ne').mdifferentiableAt univ_mem
  have hfx : f x ∈ (R.chart x).target := by
    rw [← R.apply_zero x hx]
    exact (R.chart x).map_source (R.zero_mem_source x hx)
  have hinvDiff : MDifferentiableAt J IP (R.chart x).symm (f x) :=
    ((S.contMDiffOn_chart_symm x) (f x) hfx)
      |>.mdifferentiableWithinAt (lt_of_lt_of_le zero_lt_one hn).ne'
      |>.mdifferentiableAt ((R.chart x).open_target.mem_nhds hfx)
  have hchain := mfderiv_comp_apply (I := I) (I' := J) (I'' := IP)
    (f := f) (g := (R.chart x).symm) (x := x) hinvDiff hfDiff v
  change (mfderiv J IP (R.chart x).symm (f x) (mfderiv I J f x v)).2 = 0
  rw [← hchain]
  change (mfderiv I IP (fun y ↦ (R.chart x).symm (f y)) x v).2 = 0
  rw [hderivEq, show mfderiv I IP z x = ContinuousLinearMap.inl ℝ E ℝ by
    exact mfderiv_prod_left]
  rfl

theorem not_mem_range_mfderiv_of_mem_positiveNormalHalfSpace
    (hn : (1 : ℕ∞ω) ≤ n) {x : B} {v : TangentSpace J (f x)}
    (hv : v ∈ C.positiveNormalHalfSpace x) :
    v ∉ Set.range (mfderiv I J f x) := by
  intro hvRange
  obtain ⟨w, rfl⟩ := hvRange
  have hpos : 0 < C.positiveNormalFunctional x (mfderiv I J f x w) := hv
  rw [C.positiveNormalFunctional_mfderiv_eq_zero hn x w] at hpos
  exact lt_irrefl 0 hpos

theorem exists_contMDiffSection_mem_positiveNormalHalfSpace
    [FiniteDimensional ℝ E] [IsManifold I ∞ B] [IsManifold J ∞ A]
    [SigmaCompactSpace B] [T2Space B]
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ∃ s : Cₛ^(m : ℕ∞ω)⟮I; F,
        C.continuousMap *ᵖ (TangentSpace J : A → Type _)⟯,
      ∀ x : B, s x ∈ C.positiveNormalHalfSpace x := by
  let R := C.normalAtlas
  have hn : (1 : ℕ∞ω) ≤ n := by
    exact (by simp : (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1) |>.trans hmn
  let : ∀ x : B,
      AddCommGroup ((C.continuousMap *ᵖ (TangentSpace J : A → Type _)) x) :=
    fun x ↦ inferInstanceAs (AddCommGroup (TangentSpace J (f x)))
  apply exists_contMDiffSection_forall_mem_convex_of_local I
    (C.continuousMap *ᵖ (TangentSpace J : A → Type _))
    C.positiveNormalHalfSpace C.convex_positiveNormalHalfSpace
  intro x₀
  exact ⟨R.baseSet x₀, (R.isOpen_baseSet x₀).mem_nhds (R.mem_baseSet_self x₀),
    C.localNormal x₀, C.contMDiffOn_localNormal hmn x₀,
    fun y hy ↦ C.localNormal_mem_positiveNormalHalfSpace hn hy⟩

theorem exists_contMDiff_transverseSection
    [FiniteDimensional ℝ E] [IsManifold I ∞ B] [IsManifold J ∞ A]
    [SigmaCompactSpace B] [T2Space B]
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ∃ s : Cₛ^(m : ℕ∞ω)⟮I; F,
        C.continuousMap *ᵖ (TangentSpace J : A → Type _)⟯,
      (∀ x : B, s x ∈ C.positiveNormalHalfSpace x) ∧
      (∀ x : B, s x ∉ Set.range (mfderiv I J f x)) := by
  obtain ⟨s, hs⟩ := C.exists_contMDiffSection_mem_positiveNormalHalfSpace hmn
  have hn : (1 : ℕ∞ω) ≤ n :=
    (by simp : (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1) |>.trans hmn
  exact ⟨s, hs, fun x ↦ C.not_mem_range_mfderiv_of_mem_positiveNormalHalfSpace hn (hs x)⟩

end CoorientedSmoothEmbeddingRealNormalAtlas

end DifferentialGeometry.Topology
