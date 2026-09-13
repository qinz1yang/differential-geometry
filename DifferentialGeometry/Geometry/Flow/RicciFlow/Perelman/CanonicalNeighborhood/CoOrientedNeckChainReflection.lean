import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderCoOrientationReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckAxialReflection

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M}

section MapDistinctness

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.map_cast {y : M} (h : y = x) (nk : StrongNeck S eps x t) :
    (h ▸ nk).map = nk.map := by
  cases h
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.one_lt_inv_eps (nk : StrongNeck S eps x t) : (1 : ℝ) < eps⁻¹ := by
  have h : (1 / 11 : ℝ)⁻¹ < eps⁻¹ :=
    (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 11) nk.eps_pos).2 nk.eps_small
  norm_num at h
  linarith

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.mem_source_of_abs_lt_inv (nk : StrongNeck S eps x t) {a : ℝ}
    (ha : |a| < eps⁻¹) : (nk.center, a) ∈ nk.map.source := by
  refine nk.domain ⟨trivial, ?_⟩
  rwa [abs_lt] at ha

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.axialReflection_map_ne (nk : StrongNeck S eps x t) :
    nk.axialReflection.map ≠ nk.map := by
  intro h
  have hsrc : (nk.center, (1 : ℝ)) ∈ nk.map.source :=
    nk.mem_source_of_abs_lt_inv (by rw [abs_one]; exact nk.one_lt_inv_eps)
  have hsrc' : (nk.center, (-1 : ℝ)) ∈ nk.map.source :=
    nk.mem_source_of_abs_lt_inv (by rw [abs_neg, abs_one]; exact nk.one_lt_inv_eps)
  have hkey : nk.map (nk.center, (-1 : ℝ)) = nk.map (nk.center, (1 : ℝ)) := by
    have hpt : nk.axialReflection.map (nk.center, (1 : ℝ)) = nk.map (nk.center, (1 : ℝ)) := by
      rw [h]
    rwa [StrongNeck.axialReflection_map, PartialDiffeomorph.trans_apply,
      cylinderAxialReflection_apply] at hpt
  have hinj : (nk.center, (-1 : ℝ)) = (nk.center, (1 : ℝ)) := by
    have h2 : nk.map.invFun (nk.map (nk.center, (-1 : ℝ))) =
        nk.map.invFun (nk.map (nk.center, (1 : ℝ))) := by rw [hkey]
    rw [nk.map.left_inv' hsrc', nk.map.left_inv' hsrc] at h2
    exact h2
  have : (-1 : ℝ) = 1 := congrArg Prod.snd hinj
  norm_num at this

end MapDistinctness

section ReflectionObstruction

omit [T2Space M] [SigmaCompactSpace M] in
theorem not_cylinderCoOriented_of_map_eq_axialReflection (nk : StrongNeck S eps x t)
    {Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}
    (h : nk.axialReflection.map = Ψ.trans nk.map) : ¬ CylinderCoOriented Ψ := by
  have hsource : (nk.axialReflection.map).source = (Ψ.trans nk.map).source :=
    congrArg (fun Φ : PartialDiffeomorph IC I3 Cylinder M ∞ => Φ.source) h
  have hmap : Ψ.trans nk.map = cylinderAxialReflection.trans nk.map := by
    rw [← h, StrongNeck.axialReflection_map]
  have hfun : ∀ z : Cylinder, nk.map (Ψ z) = nk.map (cylinderAxialReflection z) := by
    intro z
    have hpt : (Ψ.trans nk.map) z = (cylinderAxialReflection.trans nk.map) z := by rw [hmap]
    rwa [PartialDiffeomorph.trans_apply, PartialDiffeomorph.trans_apply] at hpt
  have hsrc0 : (nk.center, (0 : ℝ)) ∈ (nk.axialReflection.map).source :=
    nk.axialReflection.mem_source_of_abs_lt_inv (by rw [abs_zero]; exact inv_pos.mpr nk.eps_pos)
  have hwin : {a : ℝ | (nk.center, a) ∈ (nk.axialReflection.map).source} ∈ 𝓝 (0 : ℝ) :=
    (nk.axialReflection.map.open_source.preimage (Continuous.prodMk_right nk.center)).mem_nhds
      hsrc0
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨by linarith [inv_pos.mpr nk.eps_pos], inv_pos.mpr nk.eps_pos⟩
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ),
      Ψ (nk.center, a) = cylinderAxialReflection (nk.center, a) := by
    refine Filter.eventually_of_mem (Filter.inter_mem hwin (isOpen_Ioo.mem_nhds h0mem))
      fun a ha => ?_
    obtain ⟨hsrc, haIoo⟩ := ha
    have hsource_pt : (nk.center, a) ∈ (Ψ.trans nk.map).source := hsource ▸ hsrc
    rw [PartialDiffeomorph.trans_source] at hsource_pt
    obtain ⟨_, htarget⟩ := hsource_pt
    have hrefl : cylinderAxialReflection (nk.center, a) ∈ nk.map.source := by
      rw [cylinderAxialReflection_apply]
      have h1 := nk.one_lt_inv_eps
      refine nk.domain ⟨trivial, ?_⟩
      constructor <;> linarith [haIoo.1, haIoo.2, h1]
    have h3 := nk.map.left_inv' htarget
    have h4 := nk.map.left_inv' hrefl
    rw [hfun (nk.center, a)] at h3
    exact h3.symm.trans h4
  have hmem : (nk.center, (0 : ℝ)) ∈ Ψ.source := by
    have hpt : (nk.center, (0 : ℝ)) ∈ (Ψ.trans nk.map).source := hsource ▸ hsrc0
    rw [PartialDiffeomorph.trans_source] at hpt
    exact hpt.1
  exact not_cylinderCoOriented_of_eventuallyEq_axialReflection hmem hev

end ReflectionObstruction

section PositiveInstance

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.axialReflection_map_symm_apply (nk : StrongNeck S eps x t) {w : M}
    (hw : w ∈ nk.map.target) :
    nk.axialReflection.map.symm w = cylinderAxialReflection.symm (nk.map.symm w) := by
  have hsrc : nk.map.symm w ∈ nk.map.source := nk.map.map_target' hw
  rw [StrongNeck.axialReflection_map]
  conv_lhs => rw [← nk.map.right_inv' hw]
  exact PartialDiffeomorph.trans_symm_apply cylinderAxialReflection nk.map hsrc

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.axialReflection_transition_axial_fderiv_flip {nk₀ nk₁ : StrongNeck S eps x t}
    {z : Cylinder} (hz : z ∈ nk₀.map.source) (hzt : nk₀.map z ∈ nk₁.map.target) :
    fderiv ℝ (fun a : ℝ => (nk₁.axialReflection.map.symm (nk₀.map (z.1, a))).2) z.2 1 =
      -fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 := by
  have hpre : {a : ℝ | nk₀.map (z.1, a) ∈ nk₁.map.target} ∈ 𝓝 z.2 := by
    have hcurve : ContinuousAt (fun a : ℝ => (z.1, a)) z.2 :=
      (Continuous.prodMk_right z.1).continuousAt
    have hmap : ContinuousAt (nk₀.map : Cylinder → M) (z.1, z.2) :=
      nk₀.map.contMDiffOn_toFun.continuousOn.continuousAt
        (nk₀.map.open_source.mem_nhds hz)
    exact (hmap.comp hcurve).preimage_mem_nhds (nk₁.map.open_target.mem_nhds hzt)
  have hev : (fun a : ℝ => (nk₁.axialReflection.map.symm (nk₀.map (z.1, a))).2) =ᶠ[𝓝 z.2]
      fun a : ℝ => -(nk₁.map.symm (nk₀.map (z.1, a))).2 := by
    refine Filter.eventually_of_mem hpre fun a ha => ?_
    simp only [StrongNeck.axialReflection_map_symm_apply nk₁ ha, cylinderAxialReflection_symm_apply]
  have hval : (fderiv ℝ (fun a : ℝ => -(nk₁.map.symm (nk₀.map (z.1, a))).2) z.2) 1 =
      -(fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2) 1 := by
    have hfun : (fun a : ℝ => -(nk₁.map.symm (nk₀.map (z.1, a))).2) =
        -(fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) := by
      funext a
      rfl
    rw [hfun, fderiv_neg, neg_apply]
  rw [hev.fderiv_eq, hval]

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_axial_fderiv_eq_one_of_map_eq {nk₀ nk₁ : StrongNeck S eps x t}
    (h : nk₁.map = nk₀.map) {z : Cylinder} (hz : z ∈ nk₀.map.source) :
    fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 = 1 := by
  have h' : nk₁.map = cylinderIdentity.trans nk₀.map := by
    rw [cylinderIdentity_trans]
    exact h
  rw [PartialDiffeomorph.trans_symm_axial_fderiv (Φ := nk₀.map) (Ψ := nk₁.map) h' hz]
  have hfun : (fun a : ℝ => (cylinderIdentity.symm (z.1, a)).2) = fun a : ℝ => a := by
    funext a
    rfl
  rw [hfun]
  simp

end PositiveInstance

section ChainObstruction

omit [T2Space M] [SigmaCompactSpace M] in
theorem CoOrientedNeckChain.not_necks_eq_axialReflection {V : Set M}
    (c : CoOrientedNeckChain S eps t V) {i j : Fin c.count} (hij : j.val = i.val + 1)
    (hc : c.centers j = c.centers i) :
    c.necks j ≠ hc ▸ (c.necks i).axialReflection := by
  intro h
  have hmap : (c.necks j).map = ((c.necks i).axialReflection).map := by
    rw [h, StrongNeck.map_cast hc]
  have hkey : ((c.necks i).axialReflection).map =
      (c.reparam i j hij).trans (c.necks i).map := by
    rw [← hmap, c.reparam_map i j hij]
  exact (not_cylinderCoOriented_of_map_eq_axialReflection (c.necks i) hkey)
    (c.reparam_cooriented i j hij)

end ChainObstruction

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
