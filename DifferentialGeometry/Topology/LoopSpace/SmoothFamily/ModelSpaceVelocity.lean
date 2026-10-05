import DifferentialGeometry.Analysis.Calculus.SmoothExtension.LoopFamilyVelocity
import DifferentialGeometry.Topology.LoopSpace.SmoothFamily.Velocity
import DifferentialGeometry.Analysis.Calculus.Manifold.ChartReading
import DifferentialGeometry.Bundle.TangentSection.Spacetime

section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiff_loopSlice {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (z : DifferentialGeometry.Topology.loopCircle) : ContDiff ℝ ∞ (fun r : ℝ => γ r z) := by
  obtain ⟨x, -, hx⟩ := exists_lift_mem_Icc z
  have h : ContDiff ℝ ∞ (fun r : ℝ => γ r (x : DifferentialGeometry.Topology.loopCircle)) :=
    hγ.comp (contDiff_id.prodMk contDiff_const)
  simpa only [hx] using h

omit [FiniteDimensional ℝ E] in
theorem hasMFDerivWithinAt_loopSlice_of_deriv_eq {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    {X : ℝ → E → E} {t : ℝ} {z : DifferentialGeometry.Topology.loopCircle} {s : Set ℝ}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (hX : X t (γ t z) = deriv (fun r : ℝ => γ r z) t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => γ r z) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z))) := by
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => γ r z) t :=
    ((contDiff_loopSlice hγ z).differentiable (by norm_num)).differentiableAt
  have hd : HasDerivAt (fun r : ℝ => γ r z) (deriv (fun r : ℝ => γ r z) t) t :=
    hdiff.hasDerivAt
  rw [hX]
  exact hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt hd.hasDerivWithinAt

omit [FiniteDimensional ℝ E] in
theorem fderiv_graphLift_apply {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (q : ℝ × ℝ) :
    fderiv ℝ (graphLift γ) q =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q) := by
  have hΓ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q :=
    (hγ.differentiable (by norm_num)).differentiableAt
  rw [show graphLift γ = fun p : ℝ × ℝ =>
    (p.1, γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) from rfl]
  rw [(differentiableAt_fst (p := q)).fderiv_prodMk hΓ, fderiv_fst]

omit [FiniteDimensional ℝ E] in
theorem fderiv_slice_apply_zero_one_eq_deriv {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q (0, 1) =
      deriv (fun y : ℝ => γ q.1 (y : DifferentialGeometry.Topology.loopCircle)) q.2 := by
  have hΓ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q :=
    (hγ.differentiable (by norm_num)).differentiableAt
  have hin : HasFDerivAt (fun y : ℝ => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ ℝ) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have hcomp := hΓ.hasFDerivAt.comp q.2 hin
  have hslice : (fun y : ℝ => γ q.1 (y : DifferentialGeometry.Topology.loopCircle)) =
      (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) ∘
        (fun y : ℝ => (q.1, y)) := rfl
  rw [← fderiv_apply_one_eq_deriv
    (f := fun y : ℝ => γ q.1 (y : DifferentialGeometry.Topology.loopCircle)) (x := q.2), hslice, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]

omit [FiniteDimensional ℝ E] in
theorem injective_fderiv_graphLift_of_slice_deriv_ne {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    {q : ℝ × ℝ}
    (hne : deriv (fun y : ℝ => γ q.1 (y : DifferentialGeometry.Topology.loopCircle)) q.2 ≠ 0) :
    Function.Injective (fderiv ℝ (graphLift γ) q) := by
  rw [fderiv_graphLift_apply hγ q]
  intro u v huv
  have h0 : ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q))
      (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have h1 : (u - v).1 = 0 := by
    have := congrArg Prod.fst h0
    simpa using this
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q
      (u - v) = 0 := by
    have := congrArg Prod.snd h0
    simpa using this
  have h3 : (u - v).2 = 0 := by
    have hsplit0 : u - v = (0, (u - v).2) := by
      rw [← Prod.eta (u - v), h1]
    have hsm : u - v = (u - v).2 • ((0, 1) : ℝ × ℝ) := by
      rw [hsplit0]
      simp
    have hsplit : fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q
        (u - v) = (u - v).2 •
        fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle)) q (0, 1) := by
      conv_lhs => rw [hsm]
      rw [map_smul]
    have h4 : (u - v).2 •
        deriv (fun y : ℝ => γ q.1 (y : DifferentialGeometry.Topology.loopCircle)) q.2 = 0 := by
      rw [← fderiv_slice_apply_zero_one_eq_deriv hγ q, ← hsplit, h2]
    exact (smul_eq_zero.mp h4).resolve_right hne
  have hz : u - v = 0 := Prod.ext h1 h3
  exact sub_eq_zero.mp hz

theorem loopFamilyVelocityExtension_modelSpace (a b : ℝ) (γ : ℝ → DifferentialGeometry.Topology.freeLoop E)
    (hemb : ∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ := by
  obtain ⟨X, hX, hXeq⟩ := exists_contDiff_loopFamilyVelocity a b γ hemb hγ hi
  refine ⟨fun t p => (X t p : TangentSpace 𝓘(ℝ, E) p), ?_, ?_, ?_⟩
  · exact contMDiff_tangentSection_of_contDiff hX
  · intro t ht z
    exact hasMFDerivWithinAt_loopSlice_of_deriv_eq hγ (hXeq t (Ico_subset_Icc_self ht) z)
  · intro t ht z
    exact hasMFDerivWithinAt_loopSlice_of_deriv_eq hγ (hXeq t (Ioc_subset_Icc_self ht) z)

omit [FiniteDimensional ℝ E] in
private theorem deriv_loopSlice_ne_zero_of_immersedOn {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) J) :
    deriv (fun y : ℝ => γ t (y : DifferentialGeometry.Topology.loopCircle)) x ≠ 0 := by
  intro hzero
  refine hi x t ht ?_
  simp only [CurveMap.X, CurveMap.lift, curveOfLoopFamily, mfderiv_eq_fderiv]
  exact hzero

omit [FiniteDimensional ℝ E] in
theorem injective_fderiv_graphLift_of_immersedOn {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    {J : Set ℝ} (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) J)
    {x t : ℝ} (ht : t ∈ J) :
    Function.Injective (fderiv ℝ (graphLift γ) (t, x)) :=
  injective_fderiv_graphLift_of_slice_deriv_ne hγ (deriv_loopSlice_ne_zero_of_immersedOn ht hi)

omit [FiniteDimensional ℝ E] in
private theorem contDiff_translationLoops (v : E) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      (ContinuousMap.const (DifferentialGeometry.Topology.loopCircle) (q.1 • v))
        (q.2 : DifferentialGeometry.Topology.loopCircle)) := by
  have h : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.1 • v) :=
    (contDiff_fst : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.1)).smul contDiff_const
  simpa only [ContinuousMap.const_apply] using h

omit [FiniteDimensional ℝ E] in
theorem loopFamilyVelocityExtension_translation (a b : ℝ) (v : E) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b
      (fun t : ℝ => ContinuousMap.const (DifferentialGeometry.Topology.loopCircle) (t • v)) := by
  refine ⟨fun _ p => (v : TangentSpace 𝓘(ℝ, E) p), ?_, ?_, ?_⟩
  · exact contMDiff_tangentSection_of_contDiff (X := fun _ _ => v) contDiff_const
  · intro t ht z
    refine hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt ?_
    simpa [ContinuousMap.const_apply] using
      ((hasDerivAt_id t).smul_const v).hasDerivWithinAt
  · intro t ht z
    refine hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt ?_
    simpa [ContinuousMap.const_apply] using
      ((hasDerivAt_id t).smul_const v).hasDerivWithinAt

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem translation_velocity_eq {a b : ℝ} {v : E}
    {X : ℝ → (p : E) → TangentSpace 𝓘(ℝ, E) p}
    (hX : ∀ t ∈ Ico a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun s : ℝ => (ContinuousMap.const (DifferentialGeometry.Topology.loopCircle) (s • v))
          (z : DifferentialGeometry.Topology.loopCircle)) (Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (t • v)))) :
    ∀ t ∈ Ico a b, ∀ _z : DifferentialGeometry.Topology.loopCircle, X t (t • v) = v := by
  intro t ht z
  have h1 : HasFDerivWithinAt (fun s : ℝ => s • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) (Ici t) t := by
    have hd : HasDerivWithinAt (fun s : ℝ => s • v) v (Ici t) t := by
      simpa using ((hasDerivAt_id t).smul_const v).hasDerivWithinAt
    simpa only [← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hd.hasFDerivWithinAt
  have h2 : HasFDerivWithinAt (fun s : ℝ => s • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (t • v))) (Ici t) t := by
    simpa [ContinuousMap.const_apply] using (hX t ht z).hasFDerivWithinAt
  have hval := congrArg (fun L : ℝ →L[ℝ] E => L 1) ((uniqueDiffWithinAt_Ici t).eq h2 h1)
  simpa [ContinuousLinearMap.smulRight_apply] using hval

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
