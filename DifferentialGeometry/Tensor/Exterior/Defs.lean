/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Model
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]

abbrev DifferentialForm (k : ℕ) :=
  ContMDiffSection IM (EM [⋀^Fin k]→L[ℝ] ℝ) ⊤
    (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))

namespace DifferentialForm

variable {IM M k}

private lemma contMDiff_add_section {s t : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x)))
    (ht : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (t x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x + t x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  have ht' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, t x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (ht x₀)
  refine (hs'.add ht').congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_add (s x) (t x))

private lemma contMDiff_smul_section (c : ℝ) {s : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (c • s x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  refine ((contMDiffAt_const : ContMDiffAt IM 𝓘(ℝ,
    ℝ) ⊤ (fun _ : M => c) x₀).smul hs').congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_smul c (s x))

private lemma contMDiff_zero_section :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (0 : Bundle.continuousAlternatingMap ℝ
        (Fin k) EM
        (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  refine (contMDiffAt_const (c := (0 : EM [⋀^Fin k]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_zero)

instance instZero : Zero (DifferentialForm IM M k) :=
  ⟨⟨fun _ => 0, contMDiff_zero_section (IM := IM) (M := M) (k := k)⟩⟩

instance instAdd : Add (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun β.contMDiff_toFun⟩⟩

instance instNeg : Neg (DifferentialForm IM M k) :=
  ⟨fun α => ⟨fun x => (-1 : ℝ) • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) α.contMDiff_toFun⟩⟩

instance instSub : Sub (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + (-1 : ℝ) • β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun
      (contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) β.contMDiff_toFun)⟩⟩

instance instSMul : SMul ℝ (DifferentialForm IM M k) :=
  ⟨fun c α => ⟨fun x => c • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) c α.contMDiff_toFun⟩⟩

@[simp] theorem zero_apply (x : M) : (0 : DifferentialForm IM M k) x = 0 := rfl
@[simp] theorem add_apply (α β : DifferentialForm IM M k) (x : M) : (α + β) x = α x + β x := rfl
@[simp] theorem neg_apply (α : DifferentialForm IM M k) (x : M) : (-α) x = (-1 : ℝ) • α x := rfl
@[simp] theorem sub_apply (α β : DifferentialForm IM M k) (x : M) : (α - β) x = α x +
    (-1 : ℝ) • β x := rfl
@[simp] theorem smul_apply (c : ℝ) (α : DifferentialForm IM M k) (x : M) :
    (c • α) x = c • α x := rfl

instance instAddCommGroup : AddCommGroup (DifferentialForm IM M k) :=
  { zero := 0
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n α => ⟨fun x => (n : ℝ) • α x,
      contMDiff_smul_section (IM := IM) (M := M) (k := k) (n : ℝ) α.contMDiff_toFun⟩
    zsmul := fun z α => ⟨fun x => (z : ℝ) • α x,
      contMDiff_smul_section (IM := IM) (M := M) (k := k) (z : ℝ) α.contMDiff_toFun⟩
    add_assoc := by intro a b c; ext x; simp [add_assoc]
    zero_add := by intro a; ext x; simp
    add_zero := by intro a; ext x; simp
    nsmul_zero := by intro a; ext x; simp
    nsmul_succ := by intro n a; ext x; simp [Nat.cast_succ, add_smul]
    add_comm := by intro a b; ext x; simp [add_comm]
    neg_add_cancel := by
      intro a
      ext x
      simp only [add_apply, neg_apply, zero_apply]
      nth_rw 2 [show a x = (1 : ℝ) • a x from (one_smul ℝ (a x)).symm]
      rw [← add_smul]
      norm_num
    sub_eq_add_neg := by intro a b; ext x; rfl
    zsmul_zero' := by intro a; ext x; simp
    zsmul_succ' := by intro n a; ext x; simp [Nat.cast_succ, add_smul]
    zsmul_neg' := by
      intro n a
      ext x
      simp [Int.negSucc_eq, Nat.cast_succ, smul_smul] }

instance instModule : Module ℝ (DifferentialForm IM M k) :=
  { smul := (· • ·)
    smul_zero := by intro c; ext x; simp
    zero_smul := by intro a; ext x; simp
    smul_add := by intro c a b; ext x; simp [smul_add]
    add_smul := by intro c d a; ext x; simp [add_smul]
    mul_smul := by intro c d a; ext x; simp [mul_smul]
    one_smul := by intro a; ext x; simp }

noncomputable def wedge {k l : ℕ} (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) : DifferentialForm IM M (k + l) :=
  ⟨fun x => ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ), by
    intro x₀
    let e := trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hα : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x =>
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
    have hβ : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin l]→L[ℝ] ℝ) ⊤ (fun x =>
        (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, β x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (mem_baseSet_trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (β.contMDiff_toFun x₀)
    let W : (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
      wedge_productL (ContinuousLinearMap.mul ℝ ℝ)
    have hW : ContMDiffAt IM 𝓘(ℝ, (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)) ⊤ (fun _ : M => W) x₀ :=
      contMDiffAt_const
    refine ((hW.clm_apply hα).clm_apply hβ).congr_of_eventuallyEq ?_
    exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀))
      (fun x hx => by
        change ((trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀)
            ⟨x, ContinuousAlternatingMap.wedge_product (α x) (β x)
              (ContinuousLinearMap.mul ℝ ℝ)⟩).2 =
          W ((trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, α x⟩).2
            ((trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, β x⟩).2
        rw [continuousAlternatingMap_trivializationAt_apply (m := k + l) (IM := IM) (M := M)
          (x₀ := x₀) (x := x)
          (L := ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)),
          continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := α x),
          continuousAlternatingMap_trivializationAt_apply (m := l) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := β x)]
        rw [show W ((α x).compContinuousLinearMap ((trivializationAt EM
          (TangentSpace IM) x₀).symmL ℝ x))
              ((β x).compContinuousLinearMap ((trivializationAt EM
                (TangentSpace IM) x₀).symmL ℝ x)) =
              ContinuousAlternatingMap.wedge_product ((α x).compContinuousLinearMap
                ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
                ((β x).compContinuousLinearMap ((trivializationAt EM
                  (TangentSpace IM) x₀).symmL ℝ x))
                (ContinuousLinearMap.mul ℝ ℝ) from by
          simp [W, wedge_productL_apply]]
        exact (DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap
          (E := TangentSpace IM x) (E' := TangentSpace IM x)
          (g := α x) (h := β x) (A := (trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)))⟩

private def domDomCongrL {k l : ℕ} (e : Fin k ≃ Fin l) :
    (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousAlternatingMap.domDomCongr e f
      map_add' := fun f g => ContinuousAlternatingMap.domDomCongr_add e f g
      map_smul' := fun c f => by
        ext v
        simp [ContinuousAlternatingMap.domDomCongr_apply] }
    1 (fun f => by
      have hnorm : ‖ContinuousAlternatingMap.domDomCongr e f‖ = ‖f‖ := by
        change ‖(ContinuousAlternatingMap.domDomCongr e f).toContinuousMultilinearMap‖ = ‖f‖
        change ‖(f.toContinuousMultilinearMap.domDomCongr e : ContinuousMultilinearMap ℝ
          (fun _ : Fin l => EM) ℝ)‖ = ‖f‖
        rw [ContinuousMultilinearMap.norm_domDomCongr]
        rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      simp [hnorm])

noncomputable def reindex {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) :
    DifferentialForm IM M l :=
  ⟨fun x => ContinuousAlternatingMap.domDomCongr e (α x), by
    intro x₀
    let e' := trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e'
      (mem_baseSet_trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hα : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x =>
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
    have hL : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin l]→L[ℝ] ℝ) ⊤ (fun x =>
        (domDomCongrL e) ((trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := domDomCongrL e)).clm_apply hα
    refine hL.congr_of_eventuallyEq ?_
    exact eventually_of_mem (e'.open_baseSet.mem_nhds (mem_baseSet_trivializationAt
      (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀))
      (fun x hx => by
        change (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀
            ⟨x, ContinuousAlternatingMap.domDomCongr e (α x)⟩).2 =
          (domDomCongrL e) ((trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2)
        rw [continuousAlternatingMap_trivializationAt_apply (m := l) (IM := IM) (M := M)
          (x₀ := x₀) (x := x)
          (L := ContinuousAlternatingMap.domDomCongr e (α x)),
          continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := α x)]
        change (ContinuousAlternatingMap.domDomCongr e (α x)).compContinuousLinearMap
            ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) =
          ContinuousAlternatingMap.domDomCongr e ((α x).compContinuousLinearMap
            ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
        exact (domDomCongr_compContinuousLinearMap
          (E := TangentSpace IM x) (E' := TangentSpace IM x) (σ := e)
          (L := α x) (A := (trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)).symm)⟩

@[simp] theorem reindex_apply {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) (x : M) :
    (reindex e α) x = ContinuousAlternatingMap.domDomCongr e (α x) := rfl

@[simp] theorem reindex_refl (α : DifferentialForm IM M k) :
    reindex (Equiv.refl (Fin k)) α = α := by
  ext x
  simp [reindex_apply]

theorem reindex_comp {k l m : ℕ} (e : Fin k ≃ Fin l) (f : Fin l ≃ Fin m)
    (α : DifferentialForm IM M k) :
    reindex f (reindex e α) = reindex (e.trans f) α := by
  ext x
  change ContinuousAlternatingMap.domDomCongr f (ContinuousAlternatingMap.domDomCongr e (α x)) =
    ContinuousAlternatingMap.domDomCongr (e.trans f) (α x)
  ext v
  rfl

@[simp] theorem reindex_symm {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M l) :
    reindex e (reindex e.symm α) = α := by
  rw [reindex_comp e.symm e α, Equiv.symm_trans_self, reindex_refl]

@[simp] theorem reindex_symm' {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) :
    reindex e.symm (reindex e α) = α := by
  rw [reindex_comp e e.symm α, Equiv.self_trans_symm, reindex_refl]

notation:70 α " ∧ " β => DifferentialForm.wedge α β

theorem add_wedge {k l : ℕ} (α β : DifferentialForm IM M k)
    (γ : DifferentialForm IM M l) :
    DifferentialForm.wedge (α + β) γ = DifferentialForm.wedge α γ + DifferentialForm.wedge β γ := by
  ext x
  change ContinuousAlternatingMap.wedge_product (α x + β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ) =
    ContinuousAlternatingMap.wedge_product (α x) (γ x) (ContinuousLinearMap.mul ℝ ℝ) +
    ContinuousAlternatingMap.wedge_product (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.add_wedge (α x) (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_add {k l : ℕ} (α : DifferentialForm IM M k)
    (β γ : DifferentialForm IM M l) :
    DifferentialForm.wedge α (β + γ) = DifferentialForm.wedge α β + DifferentialForm.wedge α γ := by
  ext x
  change ContinuousAlternatingMap.wedge_product (α x) (β x + γ x) (ContinuousLinearMap.mul ℝ ℝ) =
    ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ) +
    ContinuousAlternatingMap.wedge_product (α x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_add (α x) (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)

theorem smul_wedge {k l : ℕ} (c : ℝ) (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) :
    DifferentialForm.wedge (c • α) β = c • DifferentialForm.wedge α β := by
  ext x
  change ContinuousAlternatingMap.wedge_product (c • α x) (β x) (ContinuousLinearMap.mul ℝ ℝ) =
    c • ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.smul_wedge c (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_smul {k l : ℕ} (c : ℝ) (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) :
    DifferentialForm.wedge α (c • β) = c • DifferentialForm.wedge α β := by
  ext x
  change ContinuousAlternatingMap.wedge_product (α x) (c • β x) (ContinuousLinearMap.mul ℝ ℝ) =
    c • ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_smul c (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_comm {k l : ℕ} (α : DifferentialForm IM M k) (β : DifferentialForm IM M l) :
    DifferentialForm.wedge α β = reindex (Fin.finAddCongr (m := l) (n := k))
      ((-1 : ℝ)^(k*l) • DifferentialForm.wedge β α) := by
  ext x
  simp only [DifferentialForm.wedge, reindex_apply, smul_apply]
  exact ContinuousAlternatingMap.wedge_antisymm (𝕜 := ℝ) (M := TangentSpace IM x)
    (m := k) (n := l) (α x) (β x)

theorem wedge_self_odd_zero {k : ℕ} (α : DifferentialForm IM M k) (hk : Odd k) :
    DifferentialForm.wedge α α = 0 := by
  ext x
  exact ContinuousAlternatingMap.wedge_self_odd_zero (M := TangentSpace IM x) (m := k)
    (α x) hk (by norm_num)

theorem wedge_assoc {k l r : ℕ} (α : DifferentialForm IM M k) (β : DifferentialForm IM M l)
    (γ : DifferentialForm IM M r) :
    reindex Fin.finAssoc.symm (DifferentialForm.wedge α (DifferentialForm.wedge β γ)) =
      DifferentialForm.wedge (DifferentialForm.wedge α β) γ := by
  ext x
  change ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
      (ContinuousAlternatingMap.wedge_product (α x)
        (ContinuousAlternatingMap.wedge_product (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ))
        (ContinuousLinearMap.mul ℝ ℝ)) =
    ContinuousAlternatingMap.wedge_product
      (ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ))
      (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_mul_assoc (M := TangentSpace IM x) (m := k) (n := l)
    (p := r) (α x) (β x) (γ x)

end DifferentialForm

end DifferentialGeometry

end
