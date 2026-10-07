import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

variable {E F H H' X M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace M] [ChartedSpace H' M]

theorem curve_velocity_not_mem_range_mfderiv_of_scalar_deriv
    {β : X → M} {B : M → ℝ} {γ : ℝ → M} {x : X} {t a b : ℝ}
    (hβ : MDifferentiableAt I J β x) (hB : MDifferentiableAt J 𝓘(ℝ, ℝ) B (β x))
    (hlevel : B ∘ β =ᶠ[𝓝 x] fun _ => a)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) J γ t) (hpoint : γ t = β x)
    (hder : HasDerivAt (B ∘ γ) b t) (hb : b ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ) J γ t ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) ∉
      Set.range (mfderiv I J β x) := by
  have hzero : mfderiv I 𝓘(ℝ, ℝ) (B ∘ β) x = 0 := by
    rw [hlevel.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
  have hchain := mfderiv_comp x hB hβ
  have hBγ : MDifferentiableAt J 𝓘(ℝ, ℝ) B (γ t) := hpoint.symm ▸ hB
  have hcurve := hBγ.hasMFDerivAt.comp t hγ.hasMFDerivAt
  let L : F →L[ℝ] ℝ := mfderiv J 𝓘(ℝ, ℝ) B (β x)
  let D : E →L[ℝ] F := mfderiv I J β x
  let vγ : F := mfderiv 𝓘(ℝ, ℝ) J γ t
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)
  have hcurve' : HasFDerivAt (B ∘ γ)
      ((show F →L[ℝ] ℝ from mfderiv J 𝓘(ℝ, ℝ) B (γ t)).comp
        (show ℝ →L[ℝ] F from mfderiv 𝓘(ℝ, ℝ) J γ t)) t := by
    convert! hcurve.hasFDerivAt
  have hrate : b = L vγ := by
    have h := hder.unique hcurve'.hasDerivAt
    have hp := mfderiv_congr_point (I := J) (I' := 𝓘(ℝ, ℝ)) (f := B) hpoint
    change b = (show F →L[ℝ] ℝ from mfderiv J 𝓘(ℝ, ℝ) B (γ t)) vγ at h
    rw [hp] at h
    exact h
  have hLD : L.comp D = 0 := hchain.symm.trans hzero
  rintro ⟨v, hv⟩
  apply hb
  rw [hrate]
  change D v = vγ at hv
  rw [← hv]
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) hLD

end DifferentialGeometry.Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {r : ℕ∞ω}

theorem mfderiv_symm_comp_mfderiv (Φ : PartialDiffeomorph I J M N r)
    (hr : r ≠ 0) {x : M} (hx : x ∈ Φ.source) :
    (show F →L[𝕜] E from mfderiv J I Φ.symm (Φ x)).comp
      (show E →L[𝕜] F from mfderiv I J Φ x) = ContinuousLinearMap.id 𝕜 E := by
  have hΦ := (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt hr
  have hΨ := (Φ.contMDiffOn_invFun.contMDiffAt
    (Φ.open_target.mem_nhds (Φ.map_source hx))).mdifferentiableAt hr
  have he : Φ.symm ∘ Φ =ᶠ[𝓝 x] id :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hx) (fun y hy => Φ.left_inv hy)
  change MDifferentiableAt J I Φ.symm (Φ x) at hΨ
  have hd := mfderiv_comp x hΨ hΦ
  rw [he.mfderiv_eq, mfderiv_id] at hd
  exact hd.symm

theorem mfderiv_comp_mfderiv_symm (Φ : PartialDiffeomorph I J M N r)
    (hr : r ≠ 0) {y : N} (hy : y ∈ Φ.target) :
    (show E →L[𝕜] F from mfderiv I J Φ (Φ.symm y)).comp
      (show F →L[𝕜] E from mfderiv J I Φ.symm y) = ContinuousLinearMap.id 𝕜 F :=
  Φ.symm.mfderiv_symm_comp_mfderiv hr hy

end PartialDiffeomorph

namespace DifferentialGeometry.Manifold

variable {E F G H H' H'' X M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H'' N] {r : ℕ∞ω}

theorem curve_velocity_not_mem_range_mfderiv_partialDiffeomorph_of_scalar_deriv
    (Φ : PartialDiffeomorph J K M N r) (hr : r ≠ 0)
    {β : X → M} {B : M → ℝ} {γ : ℝ → N} {x : X} {t a b : ℝ}
    (hβ : MDifferentiableAt I J β x) (hB : MDifferentiableAt J 𝓘(ℝ, ℝ) B (β x))
    (hlevel : B ∘ β =ᶠ[𝓝 x] fun _ => a) (hsource : β x ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) K γ t) (hpoint : γ t = Φ (β x))
    (hder : HasDerivAt ((B ∘ Φ.symm) ∘ γ) b t) (hb : b ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ) K γ t ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) ∉
      Set.range (mfderiv I K (Φ ∘ β) x) := by
  have hΦ := (Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds hsource)).mdifferentiableAt hr
  have hΨ := (Φ.contMDiffOn_invFun.contMDiffAt
    (Φ.open_target.mem_nhds (Φ.map_source hsource))).mdifferentiableAt hr
  have hB' : MDifferentiableAt K 𝓘(ℝ, ℝ) (B ∘ Φ.symm) (Φ (β x)) :=
    hB.comp_of_eq (Φ (β x)) hΨ (Φ.left_inv hsource)
  have hinv : (B ∘ Φ.symm) ∘ (Φ ∘ β) =ᶠ[𝓝 x] B ∘ β := by
    have hnear : ∀ᶠ y in 𝓝 x, β y ∈ Φ.source :=
      hβ.continuousAt (Φ.open_source.mem_nhds hsource)
    filter_upwards [hnear] with y hy
    exact congrArg B (Φ.left_inv hy)
  exact curve_velocity_not_mem_range_mfderiv_of_scalar_deriv
    (hΦ.comp x hβ) hB' (hinv.trans hlevel) hγ hpoint hder hb

variable {V Hₛ S : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace Hₛ] [TopologicalSpace S] [ChartedSpace Hₛ S]
  {L : ModelWithCorners ℝ V Hₛ} {rA : ℕ∞ω}

theorem vertical_not_mem_range_mfderiv_of_scalar_deriv
    (Φ : PartialDiffeomorph J K M N r) (hr : r ≠ 0)
    (A : PartialDiffeomorph (L.prod 𝓘(ℝ, ℝ)) K (S × ℝ) N rA) (hrA : rA ≠ 0)
    {β : X → M} {B : M → ℝ} {γ : ℝ → N} {x : X} {t a b c : ℝ}
    (hβ : MDifferentiableAt I J β x) (hB : MDifferentiableAt J 𝓘(ℝ, ℝ) B (β x))
    (hlevel : B ∘ β =ᶠ[𝓝 x] fun _ => a) (hsource : β x ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) K γ t) (hpoint : γ t = Φ (β x))
    (htarget : γ t ∈ A.target)
    (hder : HasDerivAt ((B ∘ Φ.symm) ∘ γ) b t) (hb : b ≠ 0)
    (hvelocity : (show V × ℝ from mfderiv 𝓘(ℝ, ℝ) (L.prod 𝓘(ℝ, ℝ)) (A.symm ∘ γ) t
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)) = (0, c)) :
    (0, 1) ∉ Set.range (mfderiv I (L.prod 𝓘(ℝ, ℝ)) (A.symm ∘ (Φ ∘ β)) x) := by
  have hnot := curve_velocity_not_mem_range_mfderiv_partialDiffeomorph_of_scalar_deriv
    Φ hr hβ hB hlevel hsource hγ hpoint hder hb
  have hΦ := (Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds hsource)).mdifferentiableAt hr
  have hη : MDifferentiableAt I K (Φ ∘ β) x := hΦ.comp x hβ
  have hAinv : MDifferentiableAt K (L.prod 𝓘(ℝ, ℝ)) A.symm (γ t) :=
    (A.contMDiffOn_invFun.contMDiffAt (A.open_target.mem_nhds htarget)).mdifferentiableAt hrA
  have hAinv' : MDifferentiableAt K (L.prod 𝓘(ℝ, ℝ)) A.symm (Φ (β x)) := hpoint ▸ hAinv
  let D : E →L[ℝ] G := mfderiv I K (Φ ∘ β) x
  let T : G →L[ℝ] V × ℝ := mfderiv K (L.prod 𝓘(ℝ, ℝ)) A.symm (γ t)
  let U : V × ℝ →L[ℝ] G := mfderiv (L.prod 𝓘(ℝ, ℝ)) K A (A.symm (γ t))
  let C : E →L[ℝ] V × ℝ := mfderiv I (L.prod 𝓘(ℝ, ℝ)) (A.symm ∘ (Φ ∘ β)) x
  let vγ : G := mfderiv 𝓘(ℝ, ℝ) K γ t
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)
  have hUT : U.comp T = ContinuousLinearMap.id ℝ G := A.mfderiv_comp_mfderiv_symm hrA htarget
  have hTi : Function.Injective T := by
    intro v w hvw
    have hv : U (T v) = v := congrArg (fun D : G →L[ℝ] G => D v) hUT
    have hw : U (T w) = w := congrArg (fun D : G →L[ℝ] G => D w) hUT
    exact hv.symm.trans ((congrArg U hvw).trans hw)
  have hC : C = T.comp D := by
    have h := mfderiv_comp x hAinv' hη
    have hp := mfderiv_congr_point (I := K) (I' := L.prod 𝓘(ℝ, ℝ)) (f := A.symm) hpoint
    change C = (show G →L[ℝ] V × ℝ from mfderiv K (L.prod 𝓘(ℝ, ℝ)) A.symm (Φ (β x))).comp D at h
    rw [← hp] at h
    exact h
  have hTv : T vγ = (0, c) := by
    have h := mfderiv_comp_apply t hAinv hγ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)
    exact h.symm.trans hvelocity
  change (0, 1) ∉ Set.range C
  change vγ ∉ Set.range D at hnot
  rintro ⟨v, hv⟩
  apply hnot
  refine ⟨c • v, ?_⟩
  apply hTi
  rw [← ContinuousLinearMap.comp_apply, ← hC, map_smul, hv, hTv]
  simp

end DifferentialGeometry.Manifold
