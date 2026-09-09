import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem isLocallyConstant_of_mfderiv_eq_zero_model
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : V → M}
    (hf : MDifferentiable 𝓘(ℝ, V) I f)
    (hz : ∀ r, mfderiv 𝓘(ℝ, V) I f r = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := extChartAt I (f x)
  let U : Set V := f ⁻¹' e.source
  let F : V → E := e ∘ f
  have hU : IsOpen U := by
    exact (isOpen_extChartAt_source (I := I) (f x)).preimage hf.continuous
  have hxU : x ∈ U := mem_extChartAt_source (f x)
  have hmd (r : V) (hr : r ∈ U) :
      MDifferentiableAt I 𝓘(ℝ, E) e (f r) := by
    apply mdifferentiableAt_extChartAt
    simpa only [U, e, Set.mem_preimage, extChartAt_source] using hr
  have hF : DifferentiableOn ℝ F U := by
    intro r hr
    exact ((hmd r hr).comp r (hf r)).differentiableAt.differentiableWithinAt
  have hFzero : U.EqOn (fderiv ℝ F) 0 := by
    intro r hr
    have hchain := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := I)
      (I'' := 𝓘(ℝ, E)) r (hmd r hr) (hf r)
    rw [hz r, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hchain
    exact hchain
  have hopen : IsOpen (U ∩ F ⁻¹' ({F x} : Set E)) :=
    hU.isOpen_inter_preimage_of_fderiv_eq_zero hF hFzero {F x}
  have hxmem : x ∈ U ∩ F ⁻¹' ({F x} : Set E) := ⟨hxU, rfl⟩
  filter_upwards [hopen.mem_nhds hxmem] with r hr
  exact e.injOn hr.1 hxU hr.2


private theorem product_snd_mfderiv
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (r : ℝ) (y : M) (v : TangentSpace I y) :
    mfderiv I 𝓘(ℝ, ℝ) (fun z : M => (Φ (z, r)).2) y v =
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ (y, r) (v, 0)).2 := by
  have hΦ := Φ.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hin : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) (fun z : M => (z, r)) y :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hcomp : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) (fun z : M => Φ (z, r)) y :=
    (hΦ (y, r)).comp y hin
  have h₁ := mfderiv_comp_apply y mdifferentiableAt_snd hcomp v
  have h₂ := mfderiv_comp_apply y (hΦ (y, r)) hin v
  rw [mfderiv_snd] at h₁
  rw [mfderiv_prod_left] at h₂
  exact h₁.trans (congrArg Prod.snd h₂)

private theorem product_fst_mfderiv
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (y : M) (r v : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (y, s)).1) r v =
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ (y, r) (0, v)).1 := by
  have hΦ := Φ.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hin : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (fun s : ℝ => (y, s)) r :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (fun s : ℝ => Φ (y, s)) r := (hΦ (y, r)).comp r hin
  have h₁ := mfderiv_comp_apply r mdifferentiableAt_fst hcomp v
  have h₂ := mfderiv_comp_apply r (hΦ (y, r)) hin v
  rw [mfderiv_fst] at h₁
  rw [mfderiv_prod_right] at h₂
  exact h₁.trans (congrArg Prod.fst h₂)

theorem product_snd_eq_of_mfderiv_horizontal_zero [I.Boundaryless]
    [IsManifold I 1 M] [PreconnectedSpace M]
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hzero : ∀ (x : M × ℝ) (v : TangentSpace I x.1),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (v, 0)).2 = 0)
    (y y₀ : M) (r : ℝ) : (Φ (y, r)).2 = (Φ (y₀, r)).2 := by
  have hf : MDifferentiable I 𝓘(ℝ, ℝ) (fun z : M => (Φ (z, r)).2) :=
    mdifferentiable_snd.comp ((Φ.mdifferentiable (by decide)).comp
      (mdifferentiable_id.prodMk mdifferentiable_const))
  have hz : ∀ z : M, mfderiv I 𝓘(ℝ, ℝ) (fun w : M => (Φ (w, r)).2) z = 0 := by
    intro z
    ext v
    exact (product_snd_mfderiv Φ r z v).trans (hzero (z, r) v)
  exact (isLocallyConstant_of_mfderiv_eq_zero hf hz).apply_eq_of_preconnectedSpace y y₀

theorem product_fst_eq_of_mfderiv_vertical_zero
    [IsManifold I 1 M]
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hzero : ∀ (x : M × ℝ) (v : ℝ),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (0, v)).1 = 0)
    (y : M) (r s : ℝ) : (Φ (y, r)).1 = (Φ (y, s)).1 := by
  have hf : MDifferentiable 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (y, s)).1) :=
    mdifferentiable_fst.comp ((Φ.mdifferentiable (by decide)).comp
      (mdifferentiable_const.prodMk mdifferentiable_id))
  have hz : ∀ s : ℝ, mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => (Φ (y, t)).1) s = 0 := by
    intro t
    apply ContinuousLinearMap.ext
    intro v
    exact (product_fst_mfderiv Φ y t v).trans (hzero (y, t) v)
  exact (isLocallyConstant_of_mfderiv_eq_zero_model hf hz).apply_eq_of_preconnectedSpace r s

theorem product_eq_of_mfderiv_off_diagonal_zero [I.Boundaryless]
    [IsManifold I 1 M] [PreconnectedSpace M]
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hfst : ∀ (x : M × ℝ) (v : ℝ),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (0, v)).1 = 0)
    (hsnd : ∀ (x : M × ℝ) (v : TangentSpace I x.1),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (v, 0)).2 = 0)
    (y y₀ : M) (r : ℝ) : Φ (y, r) = ((Φ (y, 0)).1, (Φ (y₀, r)).2) := by
  exact Prod.ext (product_fst_eq_of_mfderiv_vertical_zero Φ hfst y r 0)
    (product_snd_eq_of_mfderiv_horizontal_zero Φ hsnd y y₀ r)

theorem exists_prod_diffeomorph_of_coordinate_split
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ)) (y₀ : M)
    (hsplit : ∀ (y : M) (r : ℝ), Φ (y, r) = ((Φ (y, 0)).1, (Φ (y₀, r)).2)) :
    ∃ (φ : M ≃ₘ⟮I, I⟯ M) (ψ : ℝ ≃ₘ[ℝ] ℝ),
      ∀ (y : M) (r : ℝ), Φ (y, r) = (φ y, ψ r) := by
  let φ : M → M := fun y => (Φ (y, 0)).1
  let ψ : ℝ → ℝ := fun r => (Φ (y₀, r)).2
  have hφψ (y : M) (r : ℝ) : Φ (y, r) = (φ y, ψ r) := hsplit y r
  let φinv : M → M := fun y => (Φ.symm (y, ψ 0)).1
  let ψinv : ℝ → ℝ := fun r => (Φ.symm (φ y₀, r)).2
  have hφleft : Function.LeftInverse φinv φ := by
    intro y
    change (Φ.symm (φ y, ψ 0)).1 = y
    rw [← hφψ y 0, Φ.symm_apply_apply]
  have hφright : Function.RightInverse φinv φ := by
    intro y
    have h := congrArg Prod.fst (Φ.apply_symm_apply (y, ψ 0))
    rw [hφψ] at h
    exact h
  have hψleft : Function.LeftInverse ψinv ψ := by
    intro r
    change (Φ.symm (φ y₀, ψ r)).2 = r
    rw [← hφψ y₀ r, Φ.symm_apply_apply]
  have hψright : Function.RightInverse ψinv ψ := by
    intro r
    have h := congrArg Prod.snd (Φ.apply_symm_apply (φ y₀, r))
    rw [hφψ] at h
    exact h
  let φd : M ≃ₘ⟮I, I⟯ M :=
    { toFun := φ
      invFun := φinv
      left_inv := hφleft
      right_inv := hφright
      contMDiff_toFun := contMDiff_fst.comp (Φ.contMDiff.comp
        (contMDiff_id.prodMk contMDiff_const))
      contMDiff_invFun := contMDiff_fst.comp (Φ.symm.contMDiff.comp
        (contMDiff_id.prodMk contMDiff_const)) }
  let ψd : ℝ ≃ₘ[ℝ] ℝ :=
    { toFun := ψ
      invFun := ψinv
      left_inv := hψleft
      right_inv := hψright
      contMDiff_toFun := contMDiff_snd.comp (Φ.contMDiff.comp
        (contMDiff_const.prodMk contMDiff_id))
      contMDiff_invFun := contMDiff_snd.comp (Φ.symm.contMDiff.comp
        (contMDiff_const.prodMk contMDiff_id)) }
  exact ⟨φd, ψd, hφψ⟩

theorem exists_prod_diffeomorph_of_mfderiv_off_diagonal_zero [I.Boundaryless]
    [IsManifold I 1 M] [PreconnectedSpace M]
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hfst : ∀ (x : M × ℝ) (v : ℝ),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (0, v)).1 = 0)
    (hsnd : ∀ (x : M × ℝ) (v : TangentSpace I x.1),
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ x (v, 0)).2 = 0)
    (y₀ : M) :
    ∃ (φ : M ≃ₘ⟮I, I⟯ M) (ψ : ℝ ≃ₘ[ℝ] ℝ),
      ∀ (y : M) (r : ℝ), Φ (y, r) = (φ y, ψ r) :=
  exists_prod_diffeomorph_of_coordinate_split Φ y₀
    (fun y r => product_eq_of_mfderiv_off_diagonal_zero Φ hfst hsnd y y₀ r)

end DifferentialGeometry
