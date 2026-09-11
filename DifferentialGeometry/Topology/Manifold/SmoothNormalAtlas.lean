/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.NormalOrientationCover
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false

open Filter Manifold Set SignType Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x y z

namespace DifferentialGeometry.Topology

theorem deriv_pos_of_eventually_realNormalSide_eq_of_ne_zero
    {g : ℝ → ℝ}
    (hroot : g 0 = 0)
    (hside : ∀ᶠ t in nhds (0 : ℝ),
      t ≠ 0 → realNormalSide (g t) = realNormalSide t)
    (hderiv : deriv g 0 ≠ 0) :
    0 < deriv g 0 := by
  rcases lt_or_gt_of_ne hderiv with hneg | hpos
  · have hsign : ∀ᶠ t in nhds (0 : ℝ),
        sign (g t) = sign (0 - t) :=
      eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hroot
    have hall := hside.and hsign
    obtain ⟨a, b, hzero, hab⟩ := hall.exists_Ioo_subset
    let t : ℝ := b / 2
    have ht : t ∈ Ioo a b := by
      dsimp [t]
      constructor <;> linarith [hzero.1, hzero.2]
    have htpos : 0 < t := by
      dsimp [t]
      linarith [hzero.2]
    have htne : t ≠ 0 := htpos.ne'
    have hsideAt := (hab ht).1 htne
    have hnonneg : 0 ≤ g t :=
      realNormalSide_eq_false_iff.mp
        (hsideAt.trans (realNormalSide_eq_false_of_pos htpos))
    have hsignAt := (hab ht).2
    have hnegOut : g t < 0 := by
      rw [← sign_eq_neg_one_iff, hsignAt]
      exact sign_eq_neg_one_iff.mpr (by linarith)
    exact ((not_lt_of_ge hnonneg) hnegOut).elim
  · exact hpos

namespace OpenPartialHomeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def normalDeriv
    (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ)) (x : X) : ℝ :=
  deriv (fun t : ℝ ↦ (e (x, t)).2) 0

theorem normalDeriv_pos_of_hasNormalSideFlipAt_of_ne_zero
    (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ))
    {x : X}
    (hroot : (e (x, 0)).2 = 0)
    (hflip : HasNormalSideFlipAt e x false)
    (hne : normalDeriv e x ≠ 0) :
    0 < normalDeriv e x := by
  apply deriv_pos_of_eventually_realNormalSide_eq_of_ne_zero hroot
  · have htime := hflip.curry_nhds.self_of_nhds
    filter_upwards [htime] with t ht htne
    simpa using (ht htne).2
  · exact hne

set_option backward.isDefEq.respectTransparency false in
theorem normalDeriv_ne_zero_of_isLocalDiffeomorphAt_of_eventuallyEq_zeroSection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {B : Type w} [TopologicalSpace B] [ChartedSpace H B]
    {I : ModelWithCorners ℝ E H}
    (e : OpenPartialHomeomorph (B × ℝ) (B × ℝ))
    {x : B}
    (hloc : IsLocalDiffeomorphAt
      (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) 1 e (x, 0))
    (hfix : (fun y : B ↦ e (y, 0)) =ᶠ[nhds x] fun y ↦ (y, 0)) :
    normalDeriv e x ≠ 0 := by
  let IB := I
  let IP := IB.prod (modelWithCornersSelf ℝ ℝ)
  have heDiff : MDifferentiableAt IP IP e (x, 0) :=
    hloc.mdifferentiableAt one_ne_zero
  have hzeroDiff : MDifferentiableAt IB IP (fun y : B ↦ (y, (0 : ℝ))) x :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hfixDeriv :
      mfderiv IB IP (fun y : B ↦ e (y, 0)) x =
        mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x :=
    hfix.mfderiv_eq
  have hchain :
      mfderiv IB IP (fun y : B ↦ e (y, 0)) x =
        (mfderiv IP IP e (x, 0)).comp
          (mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x) := by
    exact mfderiv_comp x heDiff hzeroDiff
  have hzeroDeriv :
      mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x =
        ContinuousLinearMap.inl ℝ E ℝ := by
    exact mfderiv_prod_left
  have hfix_apply (v : TangentSpace IB x) :
      mfderiv IP IP e (x, 0)
          (mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x v) =
        mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x v := by
    calc
      _ = mfderiv IB IP (fun y : B ↦ e (y, 0)) x v :=
        (DFunLike.congr_fun hchain v).symm
      _ = _ := DFunLike.congr_fun hfixDeriv v
  let oneT : TangentSpace (modelWithCornersSelf ℝ ℝ) (0 : ℝ) := by
    change ℝ
    exact 1
  let normalT : TangentSpace IP (x, (0 : ℝ)) := by
    change E × ℝ
    exact (0, 1)
  have hnormalDeriv :
      normalDeriv e x = (mfderiv IP IP e (x, 0) normalT).2 := by
    let c : ℝ → B × ℝ := fun t ↦ (x, t)
    have hcDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) IP c 0 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hecDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) IP
        (fun t : ℝ ↦ e (x, t)) 0 :=
      heDiff.comp 0 hcDiff
    have hsndDiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ)
        (fun t : ℝ ↦ (e (x, t)).2) 0 :=
      mdifferentiableAt_snd.comp 0 hecDiff
    have hcurveDeriv :
        mfderiv (modelWithCornersSelf ℝ ℝ) IP c 0 =
          ContinuousLinearMap.inr ℝ E ℝ := by
      exact mfderiv_prod_right
    have hcurveDerivOne :
        mfderiv (modelWithCornersSelf ℝ ℝ) IP c 0 oneT = normalT := by
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
      _ = (mfderiv (modelWithCornersSelf ℝ ℝ) IP
            (fun t : ℝ ↦ e (x, t)) 0 oneT).2 := by
              have hcomp :=
                mfderiv_comp_apply 0 mdifferentiableAt_snd hecDiff oneT
              rw [mfderiv_snd] at hcomp
              exact congrArg (NormedSpace.fromTangentSpace ((e (x, 0)).2)) hcomp
      _ = (mfderiv IP IP e (x, 0)
          (mfderiv (modelWithCornersSelf ℝ ℝ) IP c 0 oneT)).2 := by
              congr 1
              simpa [c, Function.comp_def] using
                (mfderiv_comp_apply 0 heDiff hcDiff oneT)
      _ = (mfderiv IP IP e (x, 0) normalT).2 := by rw [hcurveDerivOne]
  intro hnormalZero
  let L : (E × ℝ) ≃L[ℝ] (E × ℝ) := by
    exact hloc.mfderivToContinuousLinearEquiv one_ne_zero
  have hLnormal_eq : L (0, 1) = mfderiv IP IP e (x, 0) normalT := rfl
  have hLsnd : (L (0, 1)).2 = 0 := by
    rw [hLnormal_eq, ← hnormalDeriv]
    exact hnormalZero
  let vT : TangentSpace IB x := by
    change E
    exact (L (0, 1)).1
  let v : E := (L (0, 1)).1
  have hzero_v :
      mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x vT =
        (show TangentSpace IP (x, (0 : ℝ)) from by
          change E × ℝ
          exact (v, 0)) := by
    rw [hzeroDeriv]
    rfl
  have hLv : L (v, 0) = (v, 0) := by
    change mfderiv IP IP e (x, 0) (v, 0) = (v, 0)
    calc
      _ = mfderiv IP IP e (x, 0)
          (mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x vT) := by
            congr 1
            exact hzero_v.symm
      _ = mfderiv IB IP (fun y : B ↦ (y, (0 : ℝ))) x vT := hfix_apply vT
      _ = _ := hzero_v
  have hLnormal : L (0, 1) = (v, 0) := by
    apply Prod.ext
    · rfl
    · exact hLsnd
  have heq : (v, (0 : ℝ)) = (0, 1) :=
    L.injective (hLv.trans hLnormal.symm)
  exact zero_ne_one (congrArg Prod.snd heq)

end OpenPartialHomeomorph

structure SmoothEmbeddingRealNormalAtlas
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    (n : ℕ∞ω) (f : B → A) extends EmbeddingRealNormalAtlas f where
  contMDiffOn_chart : ∀ i,
    ContMDiffOn (I.prod (modelWithCornersSelf ℝ ℝ)) J n (chart i) (chart i).source
  contMDiffOn_chart_symm : ∀ i,
    ContMDiffOn J (I.prod (modelWithCornersSelf ℝ ℝ)) n
      (chart i).symm (chart i).target

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
    (C : SmoothEmbeddingRealNormalAtlas I J n f)

theorem contMDiffOn_transition (i j : B) :
    ContMDiffOn (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) n
      (C.toEmbeddingRealNormalAtlas.transition i j)
      (C.toEmbeddingRealNormalAtlas.transition i j).source := by
  rw [EmbeddingRealNormalAtlas.transition, OpenPartialHomeomorph.trans_source]
  exact (C.contMDiffOn_chart_symm j).comp
    ((C.contMDiffOn_chart i).mono inter_subset_left) inter_subset_right

theorem contMDiffOn_transition_symm (i j : B) :
    ContMDiffOn (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) n
      (C.toEmbeddingRealNormalAtlas.transition i j).symm
      (C.toEmbeddingRealNormalAtlas.transition i j).target := by
  simpa [EmbeddingRealNormalAtlas.transition] using C.contMDiffOn_transition j i

theorem isLocalDiffeomorphAt_transition
    {m : ℕ∞ω} (hmn : m ≤ n)
    {i j : B} {q : B × ℝ}
    (hq : q ∈ (C.toEmbeddingRealNormalAtlas.transition i j).source) :
    IsLocalDiffeomorphAt
      (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) m
      (C.toEmbeddingRealNormalAtlas.transition i j) q := by
  let Φ : PartialDiffeomorph
      (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) (B × ℝ) (B × ℝ) m := {
    toPartialEquiv := (C.toEmbeddingRealNormalAtlas.transition i j).toPartialEquiv
    open_source := (C.toEmbeddingRealNormalAtlas.transition i j).open_source
    open_target := (C.toEmbeddingRealNormalAtlas.transition i j).open_target
    contMDiffOn_toFun := (C.contMDiffOn_transition i j).of_le hmn
    contMDiffOn_invFun := (C.contMDiffOn_transition_symm i j).of_le hmn }
  exact Φ.isLocalDiffeomorphAt _ _ _ hq

theorem transition_zeroSection_eventuallyEq
    {i j x : B} (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j) :
    (fun y : B ↦ C.toEmbeddingRealNormalAtlas.transition i j (y, 0)) =ᶠ[nhds x]
      fun y ↦ (y, 0) := by
  have hbase : C.baseSet i ∩ C.baseSet j ∈ nhds x :=
    (C.isOpen_baseSet i).inter (C.isOpen_baseSet j) |>.mem_nhds ⟨hxi, hxj⟩
  filter_upwards [hbase] with y hy
  exact C.toEmbeddingRealNormalAtlas.transition_apply_zero hy.1 hy.2

theorem normalDeriv_transition_ne_zero
    (hn : (1 : ℕ∞ω) ≤ n)
    {i j x : B} (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j) :
    OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x ≠ 0 := by
  apply OpenPartialHomeomorph.normalDeriv_ne_zero_of_isLocalDiffeomorphAt_of_eventuallyEq_zeroSection
    (I := I)
  · exact C.isLocalDiffeomorphAt_transition hn
      (C.toEmbeddingRealNormalAtlas.zero_mem_transition_source hxi hxj)
  · exact C.transition_zeroSection_eventuallyEq hxi hxj

theorem normalDeriv_transition_pos_of_hasNormalSideFlipAt_of_ne_zero
    {i j x : B}
    (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j)
    (hflip : HasNormalSideFlipAt
      (C.toEmbeddingRealNormalAtlas.transition i j) x false)
    (hne : OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x ≠ 0) :
    0 < OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x := by
  apply OpenPartialHomeomorph.normalDeriv_pos_of_hasNormalSideFlipAt_of_ne_zero _
  · simpa using congrArg Prod.snd
      (C.toEmbeddingRealNormalAtlas.transition_apply_zero hxi hxj)
  · exact hflip
  · exact hne

theorem normalDeriv_transition_pos_of_hasNormalSideFlipAt
    (hn : (1 : ℕ∞ω) ≤ n)
    {i j x : B}
    (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j)
    (hflip : HasNormalSideFlipAt
      (C.toEmbeddingRealNormalAtlas.transition i j) x false) :
    0 < OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x :=
  C.normalDeriv_transition_pos_of_hasNormalSideFlipAt_of_ne_zero hxi hxj hflip
    (C.normalDeriv_transition_ne_zero hn hxi hxj)

theorem normalDeriv_transition_pos_of_transitionParity_eq_false
    (hn : (1 : ℕ∞ω) ≤ n)
    {i j x : B}
    (hxi : x ∈ C.baseSet i) (hxj : x ∈ C.baseSet j)
    (hparity : C.toEmbeddingRealNormalAtlas.transitionParity i j x = false) :
    0 < OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x := by
  have hoverlap : x ∈ C.baseSet i ∩ C.baseSet j := ⟨hxi, hxj⟩
  rw [C.toEmbeddingRealNormalAtlas.transitionParity_eq_normalSideFlipAt hoverlap] at hparity
  have hflip := OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt
    (C.toEmbeddingRealNormalAtlas.transition i j)
    (C.toEmbeddingRealNormalAtlas.transition_zeroLocus_iff_zero i j)
    (C.toEmbeddingRealNormalAtlas.transitionZeroPoint i j ⟨x, hoverlap⟩)
  rw [hparity] at hflip
  exact C.normalDeriv_transition_pos_of_hasNormalSideFlipAt hn hxi hxj hflip

end SmoothEmbeddingRealNormalAtlas

noncomputable def smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f) :
    SmoothEmbeddingRealNormalAtlas
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f where
  toEmbeddingRealNormalAtlas := embeddingRealNormalAtlasOfIsImmersionOfComplement hf h
  contMDiffOn_chart := contMDiffOn_embeddingAdaptedRealNormalChart hf h
  contMDiffOn_chart_symm := contMDiffOn_symm_embeddingAdaptedRealNormalChart hf h

noncomputable def smoothSphereEmbeddingRealNormalAtlas
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {n : ℕ∞ω} {e : SphereTwo → N}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) :
    SmoothEmbeddingRealNormalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e :=
  smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement he.isEmbedding
    (isImmersionOfComplement_real_of_isSmoothEmbedding_sphereTwo he)

end DifferentialGeometry.Topology
