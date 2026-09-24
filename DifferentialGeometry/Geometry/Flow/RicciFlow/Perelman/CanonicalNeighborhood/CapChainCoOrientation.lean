import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapChainTransition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Composition

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {J₁ : ModelWithCorners ℝ E₁ H₁}
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {J₂ : ModelWithCorners ℝ E₂ H₂}
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  {H₃ : Type*} [TopologicalSpace H₃] {J₃ : ModelWithCorners ℝ E₃ H₃}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H₁ A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H₂ B]
  {C : Type*} [TopologicalSpace C] [ChartedSpace H₃ C]

theorem PartialDiffeomorph.eq_of_toPartialEquiv_eq {Φ Ψ : PartialDiffeomorph J₁ J₂ A B ∞}
    (h : Φ.toPartialEquiv = Ψ.toPartialEquiv) : Φ = Ψ :=
  (PartialDiffeomorph.mk.injEq Φ.toPartialEquiv Φ.open_source Φ.open_target Φ.contMDiffOn_toFun
    Φ.contMDiffOn_invFun Ψ.toPartialEquiv Ψ.open_source Ψ.open_target Ψ.contMDiffOn_toFun
    Ψ.contMDiffOn_invFun).mpr h

theorem PartialDiffeomorph.trans_target (Φ : PartialDiffeomorph J₁ J₂ A B ∞)
    (Ψ : PartialDiffeomorph J₂ J₃ B C ∞) :
    (Φ.trans Ψ).target = Ψ.target ∩ Ψ.symm ⁻¹' Φ.target := by
  rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target]
  rfl

end Composition

section CylinderCoOrientation

def CylinderFiberPreserving (Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞) : Prop :=
  ∀ y : Cylinder, ∀ a : ℝ, (Ψ (y.1, a)).1 = (Ψ y).1

def CylinderAxiallyIncreasing (Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞) : Prop :=
  ∀ y ∈ Ψ.source, 0 < fderiv ℝ (fun a : ℝ => (Ψ (y.1, a)).2) y.2 1

def CylinderCoOriented (Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞) : Prop :=
  CylinderFiberPreserving Ψ ∧ CylinderFiberPreserving Ψ.symm ∧ CylinderAxiallyIncreasing Ψ

theorem CylinderCoOriented.axial_fderiv_symm_pos {Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}
    (h : CylinderCoOriented Ψ) {z : Cylinder} (hz : z ∈ Ψ.target) :
    0 < fderiv ℝ (fun a : ℝ => (Ψ.symm (z.1, a)).2) z.2 1 := by
  have hmem : Ψ.symm z ∈ Ψ.source := Ψ.map_target' hz
  have hG : 0 < fderiv ℝ (fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) (Ψ.symm z).2 1 :=
    h.2.2 (Ψ.symm z) hmem
  have hcont : ∀ᶠ a : ℝ in 𝓝 z.2, (z.1, a) ∈ Ψ.target := by
    have hpre : {a : ℝ | (z.1, a) ∈ Ψ.target} ∈ 𝓝 z.2 :=
      (Ψ.open_target.preimage (Continuous.prodMk_right z.1)).mem_nhds (by simpa using hz)
    exact Filter.eventually_of_mem hpre fun _ ha => ha
  have hev : (fun a : ℝ => (Ψ ((Ψ.symm z).1, (Ψ.symm (z.1, a)).2)).2) =ᶠ[𝓝 z.2]
      fun a : ℝ => a := by
    refine Filter.eventually_of_mem hcont fun a ha => ?_
    change (Ψ ((Ψ.symm z).1, (Ψ.symm (z.1, a)).2)).2 = a
    have h1 : Ψ.symm (z.1, a) = ((Ψ.symm z).1, (Ψ.symm (z.1, a)).2) :=
      Prod.ext (h.2.1 z a) rfl
    rw [← h1]
    exact congrArg Prod.snd (Ψ.right_inv' ha)
  have hηdiff : DifferentiableAt ℝ (fun a : ℝ => (Ψ.symm (z.1, a)).2) z.2 := by
    have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun a : ℝ => (z.1, a)) z.2 :=
      (contMDiffAt_const (c := z.1)).prodMk contMDiffAt_id
    have hsymm : ContMDiffAt IC IC ∞ (Ψ.symm : Cylinder → Cylinder) (z.1, z.2) :=
      Ψ.symm.contMDiffOn_toFun.contMDiffAt (Ψ.open_target.mem_nhds hz)
    exact (((hsymm.comp z.2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) (Ψ.symm z).2 := by
    have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun b : ℝ => ((Ψ.symm z).1, b)) (Ψ.symm z).2 :=
      (contMDiffAt_const (c := (Ψ.symm z).1)).prodMk contMDiffAt_id
    have hΨ : ContMDiffAt IC IC ∞ (Ψ : Cylinder → Cylinder) (Ψ.symm z) :=
      Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hmem)
    exact (((hΨ.comp (Ψ.symm z).2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
  have hchain := fderiv_comp z.2 hGdiff hηdiff
  have hmul (L : ℝ →L[ℝ] ℝ) (c : ℝ) : L c = c * L 1 := by
    have hc : c = c • (1 : ℝ) := by simp
    conv_lhs => rw [hc]
    rw [map_smul, smul_eq_mul]
  have hid : (fderiv ℝ ((fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) ∘
      (fun a : ℝ => (Ψ.symm (z.1, a)).2)) z.2) 1 = 1 := by
    have hfun : ((fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) ∘
        (fun a : ℝ => (Ψ.symm (z.1, a)).2)) =
        (fun a : ℝ => (Ψ ((Ψ.symm z).1, (Ψ.symm (z.1, a)).2)).2) := rfl
    rw [hfun, hev.fderiv_eq]
    simp
  have hfinal : (fderiv ℝ (fun a : ℝ => (Ψ.symm (z.1, a)).2) z.2 1) *
      (fderiv ℝ (fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) (Ψ.symm z).2 1) = 1 := by
    have h4 := hid
    rw [hchain, ContinuousLinearMap.comp_apply] at h4
    rw [hmul (fderiv ℝ (fun b : ℝ => (Ψ ((Ψ.symm z).1, b)).2) (Ψ.symm z).2)
      ((fderiv ℝ (fun a : ℝ => (Ψ.symm (z.1, a)).2) z.2) 1)] at h4
    exact h4
  exact pos_of_mul_pos_left (by rw [hfinal]; norm_num) (le_of_lt hG)

end CylinderCoOrientation

section CylinderModels

def cylinderIdentity : PartialDiffeomorph IC IC Cylinder Cylinder ∞ where
  toPartialEquiv := PartialEquiv.refl Cylinder
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]

theorem cylinderIdentity_trans (Φ : PartialDiffeomorph IC I3 Cylinder N ∞) :
    cylinderIdentity.trans Φ = Φ := by
  apply PartialDiffeomorph.eq_of_toPartialEquiv_eq
  rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv]
  exact PartialEquiv.refl_trans Φ.toPartialEquiv

end CylinderModels

section CylinderCoOrientationModels

theorem cylinderIdentity_cooriented : CylinderCoOriented cylinderIdentity := by
  refine ⟨?_, ?_, ?_⟩
  · intro y a
    rfl
  · intro y a
    rfl
  · intro y hy
    simp [cylinderIdentity]

theorem cylinderAxialShift_cooriented (c : ℝ) : CylinderCoOriented (cylinderAxialShift c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y a
    rfl
  · intro y a
    rfl
  · intro y hy
    have hfun : (fun a : ℝ => ((cylinderAxialShift c) (y.1, a)).2) = fun a : ℝ => a + c := rfl
    rw [hfun]
    simp

theorem cylinderAxialShift_symm_axial_fderiv_pos (c : ℝ) (z : Cylinder) :
    0 < fderiv ℝ (fun a : ℝ => ((cylinderAxialShift c).symm (z.1, a)).2) z.2 1 :=
  CylinderCoOriented.axial_fderiv_symm_pos (cylinderAxialShift_cooriented c) (by trivial)

theorem cylinderAxialReflection_fiberPreserving :
    CylinderFiberPreserving cylinderAxialReflection := by
  intro y a
  rfl

theorem cylinderAxialReflection_symm_fiberPreserving :
    CylinderFiberPreserving cylinderAxialReflection.symm := by
  intro y a
  rfl

theorem not_cylinderCoOriented_cylinderAxialReflection (z : Cylinder) :
    ¬ CylinderCoOriented cylinderAxialReflection := by
  intro h
  have hpos := h.2.2 z (by trivial)
  rw [cylinderAxialReflection_axial_fderiv z] at hpos
  norm_num at hpos

end CylinderCoOrientationModels

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M}

section TransitionReduction

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]

theorem PartialDiffeomorph.mem_target_of_mem_trans_target
    (Φ : PartialDiffeomorph IC I3 Cylinder N ∞) (ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞)
    {z : Cylinder} (hz : z ∈ Φ.source)
    (hzt : Φ z ∈ (ψ.trans Φ).target) : z ∈ ψ.target := by
  rw [PartialDiffeomorph.trans_target] at hzt
  have h2 : Φ.symm (Φ z) ∈ ψ.target := hzt.2
  have h3 : Φ.symm (Φ z) = z := PartialEquiv.left_inv' _ hz
  rwa [h3] at h2

theorem PartialDiffeomorph.trans_symm_axial_fderiv {Φ Ψ : PartialDiffeomorph IC I3 Cylinder N ∞}
    {ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞} (h : Ψ = ψ.trans Φ) {z : Cylinder}
    (hz : z ∈ Φ.source) :
    fderiv ℝ (fun a : ℝ => (Ψ.symm (Φ (z.1, a))).2) z.2 1 =
      fderiv ℝ (fun a : ℝ => (ψ.symm (z.1, a)).2) z.2 1 := by
  have hev : (fun a : ℝ => (Ψ.symm (Φ (z.1, a))).2) =ᶠ[𝓝 z.2]
      fun a : ℝ => (ψ.symm (z.1, a)).2 := by
    refine Filter.eventually_of_mem (U := {a : ℝ | (z.1, a) ∈ Φ.source}) ?_ ?_
    · refine (Φ.open_source.preimage ?_).mem_nhds ?_
      · exact Continuous.prodMk_right z.1
      · simpa using hz
    · intro a ha
      rw [h]
      exact congrArg Prod.snd (PartialDiffeomorph.trans_symm_apply ψ Φ ha)
  rw [hev.fderiv_eq]

end TransitionReduction

structure CoOrientedNeckChain (S : SolutionOn (I := I3) (M := M) D) (eps t : ℝ) (V : Set M) where
  count : ℕ
  count_pos : 0 < count
  centers : Fin count → M
  necks : ∀ i, StrongNeck S eps (centers i) t
  lo : Fin count → ℝ
  hi : Fin count → ℝ
  lo_lt_hi : ∀ i, lo i < hi i
  inside : ∀ i, Set.univ ×ˢ Set.Icc (lo i) (hi i) ⊆ (necks i).map.source
  swept_eq : V = ⋃ i, (necks i).map '' (Set.univ ×ˢ Set.Icc (lo i) (hi i))
  reparam : ∀ i j : Fin count, j.val = i.val + 1 →
    PartialDiffeomorph IC IC Cylinder Cylinder ∞
  reparam_map : ∀ i j hij, (necks j).map = (reparam i j hij).trans (necks i).map
  reparam_cooriented : ∀ i j hij, CylinderCoOriented (reparam i j hij)

omit [T2Space M] [SigmaCompactSpace M] in
theorem CoOrientedNeckChain.transition_axial_fderiv_pos {V : Set M}
    (c : CoOrientedNeckChain S eps t V) {i j : Fin c.count} (hij : j.val = i.val + 1)
    {z : Cylinder} (hz : z ∈ (c.necks i).map.source)
    (hzt : (c.necks i).map z ∈ (c.necks j).map.target) :
    0 < fderiv ℝ (fun a : ℝ => ((c.necks j).map.symm ((c.necks i).map (z.1, a))).2) z.2 1 := by
  have hmap : (c.necks j).map = (c.reparam i j hij).trans (c.necks i).map := c.reparam_map i j hij
  have hzψ : z ∈ (c.reparam i j hij).target :=
    PartialDiffeomorph.mem_target_of_mem_trans_target (c.necks i).map (c.reparam i j hij) hz
      (by rw [← hmap]; exact hzt)
  rw [PartialDiffeomorph.trans_symm_axial_fderiv hmap hz]
  exact CylinderCoOriented.axial_fderiv_symm_pos (c.reparam_cooriented i j hij) hzψ

omit [T2Space M] [SigmaCompactSpace M] in
noncomputable def CoOrientedNeckChain.toOrderedNeckChain {V : Set M}
    (c : CoOrientedNeckChain S eps t V) : OrderedNeckChain S eps t V where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks := c.necks
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := fun _ _ hij _ hz hzt =>
    CoOrientedNeckChain.transition_axial_fderiv_pos c hij hz hzt

omit [T2Space M] [SigmaCompactSpace M] in
noncomputable def CoOrientedNeckChain.pairOfMapEq {eps t : ℝ} {x : M}
    (nk₀ nk₁ : StrongNeck S eps x t) (h : nk₁.map = nk₀.map) :
    CoOrientedNeckChain S eps t (nk₀.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) where
  count := 2
  count_pos := by norm_num
  centers := fun _ => x
  necks := fun i => if i = 0 then nk₀ else nk₁
  lo := fun _ => 0
  hi := fun _ => 1
  lo_lt_hi := fun _ => by norm_num
  inside := fun i => by
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact nk₀.tube_window_subset_source
    · rw [if_neg h0]; exact nk₁.tube_window_subset_source
  swept_eq := by
    refine Eq.symm ?_
    apply le_antisymm
    · intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨i, hi⟩ := hy
      by_cases h0 : i = 0
      · rw [if_pos h0] at hi; exact hi
      · rw [if_neg h0] at hi; rwa [h] at hi
    · intro y hy
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hy⟩
  reparam := fun _ _ _ => cylinderIdentity
  reparam_map := fun i j hij => by
    have hi : i = 0 := by
      fin_cases i
      · rfl
      · fin_cases j <;> simp at hij
    subst hi
    have hj : j = 1 := by
      fin_cases j
      · simp at hij
      · rfl
    subst hj
    simpa [h] using (cylinderIdentity_trans nk₀.map).symm
  reparam_cooriented := fun _ _ _ => cylinderIdentity_cooriented

omit [T2Space M] [SigmaCompactSpace M] in
theorem nonempty_coOrientedNeckChain_of_map_eq {eps t : ℝ} {x : M}
    (nk₀ nk₁ : StrongNeck S eps x t) (h : nk₁.map = nk₀.map) :
    Nonempty (CoOrientedNeckChain S eps t
      (nk₀.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))) :=
  ⟨CoOrientedNeckChain.pairOfMapEq nk₀ nk₁ h⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
