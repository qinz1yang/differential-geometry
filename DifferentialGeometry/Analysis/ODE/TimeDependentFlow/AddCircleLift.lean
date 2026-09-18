import DifferentialGeometry.Analysis.ODE.Regularity.VariationalConvergence
import DifferentialGeometry.Topology.Manifold.AddCircle.AffinePeriodicLift
import Mathlib.Analysis.ODE.Basic

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace AddCircle

theorem exists_affine_periodic_integralCurve_lift
    {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ)}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => F q.1 q.2) (Icc a b ×ˢ univ))
    (hF0 : ∀ z, F a z = z)
    {β : ℝ → AddCircle (1 : ℝ) → ℝ}
    (hode : ∀ t ∈ Icc a b, ∀ z,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F s z) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (β t (F t z) • parameterTangent (F t z)))) :
    ∃ γ : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (Function.uncurry γ) (univ ×ˢ Icc a b) ∧
      (∀ x t, t ∈ Icc a b → (γ x t : AddCircle (1 : ℝ)) = F t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b → γ (x + 1) t = γ x t + 1) ∧
      (∀ x, γ x a = x) ∧
      ∀ x, IsIntegralCurveOn (γ x) (fun t y => β t (y : AddCircle (1 : ℝ))) (Icc a b) := by
  let f : ℝ × ℝ → AddCircle (1 : ℝ) := fun q => F q.2 (q.1 : AddCircle (1 : ℝ))
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ Icc a b) := by
    have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × ℝ => (q.2, (q.1 : AddCircle (1 : ℝ)))) :=
      contDiff_snd.contMDiff.prodMk (contMDiff_coe.comp contDiff_fst.contMDiff)
    exact hF.comp hp.contMDiffOn (fun q hq => ⟨hq.2, mem_univ _⟩)
  have hper : ∀ q : ℝ × ℝ, f (q.1 + 1, q.2) = f q := by
    intro q
    simp only [f, coe_add_period]
  obtain ⟨g, hg, hcoe, hperiod, hinitial⟩ :=
    exists_contDiffOn_affine_periodic_lift_of_initial_identity hab hf hper
      (fun x => hF0 (x : AddCircle (1 : ℝ)))
  refine ⟨fun x t => g (x, t), hg, ?_, ?_, hinitial, ?_⟩
  · exact fun x t ht => hcoe (x, t) ⟨mem_univ x, ht⟩
  · exact fun x t ht => hperiod (x, t) ⟨mem_univ x, ht⟩
  · intro x
    rcases hab.eq_or_lt with rfl | hab
    · intro t ht
      have ht : t = a := by simpa only [Icc_self, mem_singleton_iff] using ht
      subst t
      simpa only [Icc_self] using
        (show HasDerivWithinAt (fun s => g (x, s))
          (β a (g (x, a) : AddCircle (1 : ℝ))) {a} a from
          HasFDerivWithinAt.singleton)
    · intro t ht
      have hd : DifferentiableWithinAt ℝ (fun s => g (x, s)) (Icc a b) t :=
        ((hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun s hs => ⟨mem_univ x, hs⟩)) t ht).differentiableWithinAt (by simp)
      have hlocal : (fun s => (g (x, s) : AddCircle (1 : ℝ))) =ᶠ[𝓝[Icc a b] t]
          (fun s => F s (x : AddCircle (1 : ℝ))) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hcoe (x, s) ⟨mem_univ x, hs⟩
      have hder := hasDerivWithinAt_of_local_lift ht (uniqueDiffOn_Icc hab t ht)
        hd hlocal (hode t ht (x : AddCircle (1 : ℝ)))
      have hvalue : (g (x, t) : AddCircle (1 : ℝ)) = F t (x : AddCircle (1 : ℝ)) :=
        hcoe (x, t) ⟨mem_univ x, ht⟩
      rw [← hvalue] at hder
      exact hder

end AddCircle

end

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace AddCircle

theorem exists_affine_periodic_integralCurve_lift_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {a b : ℝ} (hab : a ≤ b)
    {F : ι → ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ)}
    {FInf : ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ)}
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => F i q.1 q.2) (Icc a b ×ˢ univ))
    (hFInf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => FInf q.1 q.2) (Icc a b ×ˢ univ))
    (hF0 : ∀ i z, F i a z = z) (hFInf0 : ∀ z, FInf a z = z)
    {β : ι → ℝ → AddCircle (1 : ℝ) → ℝ} {βInf : ℝ → AddCircle (1 : ℝ) → ℝ}
    (hβ : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => β i q.1 q.2) (Icc a b ×ˢ univ))
    (hβInf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => βInf q.1 q.2) (Icc a b ×ˢ univ))
    (hode : ∀ i t, t ∈ Icc a b → ∀ z,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F i s z) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (β i t (F i t z) • parameterTangent (F i t z))))
    (hodeInf : ∀ t ∈ Icc a b, ∀ z,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => FInf s z) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (βInf t (FInf t z) • parameterTangent (FInf t z))))
    (hv : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => β i q.2 (q.1 : AddCircle (1 : ℝ)))
      (fun q : ℝ × ℝ => βInf q.2 (q.1 : AddCircle (1 : ℝ)))
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hDv : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ))) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hD₂v : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) =>
        fderiv ℝ (fderiv ℝ (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ)))) q.1)
      (fun q : ℝ × ℝ =>
        fderiv ℝ (fderiv ℝ (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ)))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ∃ (γ : ι → ℝ → ℝ → ℝ) (γInf : ℝ → ℝ → ℝ),
      (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b) ∧
      (∀ i x t, t ∈ Icc a b →
        (γ i x t : AddCircle (1 : ℝ)) = F i t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b →
        (γInf x t : AddCircle (1 : ℝ)) = FInf t (x : AddCircle (1 : ℝ))) ∧
      (∀ i x t, t ∈ Icc a b → γ i (x + 1) t = γ i x t + 1) ∧
      (∀ x t, t ∈ Icc a b → γInf (x + 1) t = γInf x t + 1) ∧
      (∀ i x, γ i x a = x) ∧ (∀ x, γInf x a = x) ∧
      (∀ i x, IsIntegralCurveOn (γ i x)
        (fun t y => β i t (y : AddCircle (1 : ℝ))) (Icc a b)) ∧
      (∀ x, IsIntegralCurveOn (γInf x)
        (fun t y => βInf t (y : AddCircle (1 : ℝ))) (Icc a b)) ∧
      ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) =>
          DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve (γ i) q.1 q.2)
        (fun q : ℝ × ℝ =>
          DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve γInf q.1 q.2)
        l (K ×ˢ Icc a b) := by
  classical
  choose γ hγsmooth hγcoe hγperiod hγ0 hγode using
    fun i => exists_affine_periodic_integralCurve_lift hab (hF i) (hF0 i) (hode i)
  obtain ⟨γInf, hγInfSmooth, hγInfCoe, hγInfPeriod, hγInf0, hγInfOde⟩ :=
    exists_affine_periodic_integralCurve_lift hab hFInf hFInf0 hodeInf
  refine ⟨γ, γInf, hγsmooth, hγInfSmooth, hγcoe, hγInfCoe, hγperiod,
    hγInfPeriod, hγ0, hγInf0, hγode, hγInfOde, ?_⟩
  intro K hK
  have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ℝ => (q.1, (q.2 : AddCircle (1 : ℝ)))) :=
    contDiff_fst.contMDiff.prodMk (contMDiff_coe.comp contDiff_snd.contMDiff)
  have hβreal (i : ι) : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => β i q.1 (q.2 : AddCircle (1 : ℝ))) (Icc a b ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.mp
      ((hβ i).comp hp.contMDiffOn (fun q hq => ⟨hq.1, mem_univ _⟩))
  have hβInfReal : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => βInf q.1 (q.2 : AddCircle (1 : ℝ))) (Icc a b ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.mp
      (hβInf.comp hp.contMDiffOn (fun q hq => ⟨hq.1, mem_univ _⟩))
  have hper (i : ι) (t : ℝ) :
      Function.Periodic (fun x : ℝ => β i t (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    simp only [coe_add_period]
  have hperInf (t : ℝ) :
      Function.Periodic (fun x : ℝ => βInf t (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    simp only [coe_add_period]
  exact DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve_tendstoUniformlyOn_of_periodic
    (v := fun i t x => β i t (x : AddCircle (1 : ℝ)))
    (vInf := fun t x => βInf t (x : AddCircle (1 : ℝ))) hab hK hβreal hβInfReal
    (fun i t _ => hper i t) (fun t _ => hperInf t)
    hγsmooth hγInfSmooth (fun i x => ⟨hγ0 i x, hγode i x⟩)
    (fun x => ⟨hγInf0 x, hγInfOde x⟩) hv hDv hD₂v

end AddCircle

end

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace AddCircle

theorem exists_affine_periodic_integralCurve_lift_iteratedFDeriv_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {a b : ℝ} (hab : a ≤ b)
    {F : ι → ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ)}
    {FInf : ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ)}
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => F i q.1 q.2) (Icc a b ×ˢ univ))
    (hFInf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => FInf q.1 q.2) (Icc a b ×ˢ univ))
    (hF0 : ∀ i z, F i a z = z) (hFInf0 : ∀ z, FInf a z = z)
    {β : ι → ℝ → AddCircle (1 : ℝ) → ℝ} {βInf : ℝ → AddCircle (1 : ℝ) → ℝ}
    (hβ : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => β i q.1 q.2) (Icc a b ×ˢ univ))
    (hβInf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => βInf q.1 q.2) (Icc a b ×ˢ univ))
    (hode : ∀ i t, t ∈ Icc a b → ∀ z,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F i s z) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (β i t (F i t z) • parameterTangent (F i t z))))
    (hodeInf : ∀ t ∈ Icc a b, ∀ z,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => FInf s z) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (βInf t (FInf t z) • parameterTangent (FInf t z))))
    (hconv : ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) =>
        iteratedFDeriv ℝ k (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ))) q.1)
      (fun q : ℝ × ℝ =>
        iteratedFDeriv ℝ k (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ∃ (γ : ι → ℝ → ℝ → ℝ) (γInf : ℝ → ℝ → ℝ),
      (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b) ∧
      (∀ i x t, t ∈ Icc a b →
        (γ i x t : AddCircle (1 : ℝ)) = F i t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b →
        (γInf x t : AddCircle (1 : ℝ)) = FInf t (x : AddCircle (1 : ℝ))) ∧
      (∀ i x t, t ∈ Icc a b → γ i (x + 1) t = γ i x t + 1) ∧
      (∀ x t, t ∈ Icc a b → γInf (x + 1) t = γInf x t + 1) ∧
      (∀ i x, γ i x a = x) ∧ (∀ x, γInf x a = x) ∧
      (∀ i x, IsIntegralCurveOn (γ i x)
        (fun t y => β i t (y : AddCircle (1 : ℝ))) (Icc a b)) ∧
      (∀ x, IsIntegralCurveOn (γInf x)
        (fun t y => βInf t (y : AddCircle (1 : ℝ))) (Icc a b)) ∧
      ∀ K : Set ℝ, IsCompact K → ∀ k : ℕ, TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (fun x => γ i x q.2) q.1)
        (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (fun x => γInf x q.2) q.1)
        l (K ×ˢ Icc a b) := by
  classical
  choose γ hγsmooth hγcoe hγperiod hγ0 hγode using
    fun i => exists_affine_periodic_integralCurve_lift hab (hF i) (hF0 i) (hode i)
  obtain ⟨γInf, hγInfSmooth, hγInfCoe, hγInfPeriod, hγInf0, hγInfOde⟩ :=
    exists_affine_periodic_integralCurve_lift hab hFInf hFInf0 hodeInf
  refine ⟨γ, γInf, hγsmooth, hγInfSmooth, hγcoe, hγInfCoe, hγperiod,
    hγInfPeriod, hγ0, hγInf0, hγode, hγInfOde, ?_⟩
  intro K hK k
  have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ℝ => (q.1, (q.2 : AddCircle (1 : ℝ)))) :=
    contDiff_fst.contMDiff.prodMk (contMDiff_coe.comp contDiff_snd.contMDiff)
  have hβreal (i : ι) : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => β i q.1 (q.2 : AddCircle (1 : ℝ))) (Icc a b ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.mp
      ((hβ i).comp hp.contMDiffOn (fun q hq => ⟨hq.1, mem_univ _⟩))
  have hβInfReal : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => βInf q.1 (q.2 : AddCircle (1 : ℝ))) (Icc a b ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.mp
      (hβInf.comp hp.contMDiffOn (fun q hq => ⟨hq.1, mem_univ _⟩))
  have hper (i : ι) (t : ℝ) :
      Function.Periodic (fun x : ℝ => β i t (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    simp only [coe_add_period]
  have hperInf (t : ℝ) :
      Function.Periodic (fun x : ℝ => βInf t (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    simp only [coe_add_period]
  exact DifferentialGeometry.Analysis.ODE.Flow.iteratedFDeriv_integralCurve_tendstoUniformlyOn_of_periodic
    (v := fun i t x => β i t (x : AddCircle (1 : ℝ)))
    (vInf := fun t x => βInf t (x : AddCircle (1 : ℝ))) hab zero_lt_one hβreal hβInfReal
    (fun i t _ => hper i t) (fun t _ => hperInf t)
    hγsmooth hγInfSmooth (fun i x => ⟨hγ0 i x, hγode i x⟩)
    (fun x => ⟨hγInf0 x, hγInfOde x⟩) hconv hK k

end AddCircle

end
