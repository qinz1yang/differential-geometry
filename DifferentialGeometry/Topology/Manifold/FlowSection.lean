/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.TransverseDerivative
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse

/-! Local smooth coordinates obtained by flowing a transverse arc. -/

open Set Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem not_mem_range_mfderiv_of_level {f : M → ℝ} {A : ℝ → M} {s c : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (A s))
    (hA : MDifferentiableAt 𝓘(ℝ, ℝ) I A s)
    (hlevel : f ∘ A =ᶠ[𝓝 s] fun _ => c) {u : TangentSpace I (A s)}
    (hu : mvfderiv I f (A s) u ≠ 0) : u ∉ range (mfderiv 𝓘(ℝ, ℝ) I A s) := by
  rintro ⟨r, hr⟩
  apply hu
  rw [← hr]
  change mfderiv I 𝓘(ℝ, ℝ) f (A s) (mfderiv 𝓘(ℝ, ℝ) I A s r) = 0
  rw [← mfderiv_comp_apply s hf hA r, hlevel.mfderiv_eq, mfderiv_const]
  rfl

private def timeTranslation (t : ℝ) :
    Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun z := (z.1, z.2 - t)
  invFun z := (z.1, z.2 + t)
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)

theorem isLocalDiffeomorphAt_flow_of_transverse
    (hdim : Module.finrank ℝ E = 2)
    (w : (x : M) → TangentSpace I x)
    (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
    (hwc : HasCompactSupport w) {A : ℝ → M} {S : Set ℝ} (hS : IsOpen S)
    (hA : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ A S) {s : ℝ} (hs : s ∈ S)
    (himm : Injective (mfderiv 𝓘(ℝ, ℝ) I A s))
    (htrans : w (A s) ∉ range (mfderiv 𝓘(ℝ, ℝ) I A s)) (t : ℝ) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => Diffeomorph.compactSupportFlow w hw hwc z.2 (A z.1)) (s, t) := by
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  let F : ℝ × ℝ → M := fun z => Φ z.2 (A z.1)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F (S ×ˢ univ) :=
    (Diffeomorph.contMDiff_compactSupportFlow w hw hwc).comp_contMDiffOn
      (contMDiffOn_snd.prodMk (hA.comp contMDiffOn_fst (fun _ hz => hz.1)))
  have hz : (fun u => F (u, 0)) = A := by
    funext u
    exact DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) (A u)
  have ht : mfderiv 𝓘(ℝ, ℝ) I (fun u => F (s, u)) 0 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (w (A s)) := by
    have hh := (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (A s) 0).mfderiv
    have he : Diffeomorph.compactSupportFlow w hw hwc 0 (A s) = A s :=
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) (A s)
    change mfderiv 𝓘(ℝ, ℝ) I (fun t => Φ t (A s)) 0 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (w (Φ 0 (A s))) at hh
    rw [show Φ 0 (A s) = A s from he] at hh
    exact hh
  let L := DifferentialGeometry.Topology.ContinuousLinearMap.transverseEquiv (E := ℝ) (F := E)
    (mfderiv 𝓘(ℝ, ℝ) I A s) (w (A s)) himm htrans (by simpa using hdim)
  have hd : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I F (s, 0) = L.toContinuousLinearMap := by
    ext z
    rw [mfderiv_prod_eq_add_apply
      ((hF.contMDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hs, mem_univ _⟩)).mdifferentiableAt
        (by simp)), hz, ht]
    rfl
  have hzero : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F (s, 0) :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      (hS.prod isOpen_univ) ⟨hs, mem_univ _⟩ hF ⟨L, hd.symm⟩
  have hshift : timeTranslation t (s, t) = (s, 0) := by
    change (s, t - t) = (s, 0)
    rw [sub_self]
  have hcomp := (timeTranslation t).isLocalDiffeomorph (s, t) |>.comp I M
    (hshift.symm ▸ hzero)
  have htotal := hcomp.comp I M ((Φ t).isLocalDiffeomorph _)
  convert htotal using 1
  funext z
  change Φ z.2 (A z.1) = Φ t (Φ (z.2 - t) (A z.1))
  have hh : Φ (z.2 - t + t) (A z.1) = Φ t (Φ (z.2 - t) (A z.1)) :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add w hw hwc (z.2 - t) t) (A z.1)
  simpa only [sub_add_cancel] using hh

theorem isLocalDiffeomorphAt_rescaled_flow_of_transverse
    (hdim : Module.finrank ℝ E = 2)
    (w : (x : M) → TangentSpace I x)
    (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
    (hwc : HasCompactSupport w) {A : ℝ → M} {S : Set ℝ} (hS : IsOpen S)
    (hA : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ A S) {s : ℝ} (hs : s ∈ S)
    (himm : Injective (mfderiv 𝓘(ℝ, ℝ) I A s))
    (htrans : w (A s) ∉ range (mfderiv 𝓘(ℝ, ℝ) I A s))
    {τ : ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ S) (hτs : τ s ≠ 0) (t : ℝ) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => Diffeomorph.compactSupportFlow w hw hwc (z.2 * τ z.1) (A z.1))
      (s, t) := by
  let h : ℝ × ℝ → ℝ := fun z => z.2 * τ z.1
  have hh : ContDiffOn ℝ ∞ h (S ×ˢ univ) :=
    contDiffOn_snd.mul (hτ.comp contDiffOn_fst (fun _ hz => hz.1))
  have hd : fderiv ℝ h (s, t) (0, 1) ≠ 0 := by
    have hsmooth := hh.contDiffAt ((hS.prod isOpen_univ).mem_nhds
      (show (s, t) ∈ S ×ˢ univ from ⟨hs, mem_univ _⟩))
    have h₁ := (hsmooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
    have h₂ : HasDerivAt (fun u : ℝ => u * τ s) (τ s) t := by
      simpa using (hasDerivAt_id t).mul_const (τ s)
    exact (h₁.unique h₂).trans_ne hτs
  obtain ⟨e, hep, _, he, hei, heq, _⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_preserving_parameter hh
      (hS.prod isOpen_univ) ⟨hs, mem_univ _⟩ hd
  let d : PartialDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (ℝ × ℝ) (ℝ × ℝ) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      exact (he.fst.contMDiffOn.comp
        (contMDiffOn_fst.prodMk_space contMDiffOn_snd) (fun _ hz => hz)).prodMk
          (he.snd.contMDiffOn.comp
            (contMDiffOn_fst.prodMk_space contMDiffOn_snd) (fun _ hz => hz))
    contMDiffOn_invFun := by
      exact (hei.fst.contMDiffOn.comp
        (contMDiffOn_fst.prodMk_space contMDiffOn_snd) (fun _ hz => hz)).prodMk
          (hei.snd.contMDiffOn.comp
            (contMDiffOn_fst.prodMk_space contMDiffOn_snd) (fun _ hz => hz)) }
  have hloc : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun z : ℝ × ℝ => (z.1, h z)) (s, t) :=
    ⟨d, hep, fun z _ => (heq z).symm⟩
  exact hloc.comp I M (isLocalDiffeomorphAt_flow_of_transverse hdim w hw hwc hS hA hs
    himm htrans (t * τ s))

end DifferentialGeometry.Topology.Manifold
