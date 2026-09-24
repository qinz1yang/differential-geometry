import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section CylinderReparametrization

def cylinderAxialReflection : PartialDiffeomorph IC IC Cylinder Cylinder ∞ where
  toPartialEquiv :=
    { toFun := fun y : Cylinder => (y.1, -y.2)
      invFun := fun y : Cylinder => (y.1, -y.2)
      source := Set.univ
      target := Set.univ
      map_source' := fun _ _ => trivial
      map_target' := fun _ _ => trivial
      left_inv' := fun _ _ => by simp
      right_inv' := fun _ _ => by simp }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_fst.prodMk (contMDiff_snd.neg)).contMDiffOn
  contMDiffOn_invFun := (contMDiff_fst.prodMk (contMDiff_snd.neg)).contMDiffOn

@[simp]
theorem cylinderAxialReflection_apply (y : Cylinder) :
    cylinderAxialReflection y = (y.1, -y.2) := rfl

theorem cylinderAxialReflection_symm_apply (y : Cylinder) :
    cylinderAxialReflection.symm y = (y.1, -y.2) := rfl

theorem cylinderAxialReflection_axial_fderiv (z : Cylinder) :
    fderiv ℝ (fun a : ℝ => (cylinderAxialReflection (z.1, a)).2) z.2 1 = -1 := by
  have h : (fun a : ℝ => (cylinderAxialReflection (z.1, a)).2) = fun a : ℝ => -a := by
    funext a
    rw [cylinderAxialReflection_apply]
  rw [h]
  simp

def cylinderAxialReflectionTangent (y : Cylinder) (v : TangentSpace IC y) :
    TangentSpace IC (cylinderAxialReflection y) :=
  (v.1, -v.2)

theorem CylinderReference.inner_axialReflection (h : CylinderReference) {s : ℝ} (hs : s ≤ 0)
    (y : Cylinder) (v w : TangentSpace IC y) :
    (h.metric s).inner (cylinderAxialReflection y)
        (cylinderAxialReflectionTangent y v) (cylinderAxialReflectionTangent y w) =
      (h.metric s).inner y v w := by
  rw [h.inner_eq s hs (cylinderAxialReflection y) _ _, h.inner_eq s hs y v w]
  simp only [cylinderAxialReflection_apply, cylinderAxialReflectionTangent, neg_mul_neg]
  ac_rfl

def cylinderAxialShift (c : ℝ) : PartialDiffeomorph IC IC Cylinder Cylinder ∞ where
  toPartialEquiv :=
    { toFun := fun y : Cylinder => (y.1, y.2 + c)
      invFun := fun y : Cylinder => (y.1, y.2 - c)
      source := Set.univ
      target := Set.univ
      map_source' := fun _ _ => trivial
      map_target' := fun _ _ => trivial
      left_inv' := fun _ _ => by simp
      right_inv' := fun _ _ => by simp }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)).contMDiffOn
  contMDiffOn_invFun := (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)).contMDiffOn

theorem cylinderAxialShift_symm_axial_fderiv (c : ℝ) (z : Cylinder) :
    fderiv ℝ (fun a : ℝ => ((cylinderAxialShift c).symm (z.1, a)).2) z.2 1 = 1 := by
  have h : (fun a : ℝ => ((cylinderAxialShift c).symm (z.1, a)).2) = fun a : ℝ => a - c := rfl
  rw [h]
  simp

end CylinderReparametrization

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

theorem PartialDiffeomorph.trans_symm_apply (Φ : PartialDiffeomorph J₁ J₂ A B ∞)
    (Ψ : PartialDiffeomorph J₂ J₃ B C ∞) {y : B} (hy : y ∈ Ψ.source) :
    (Φ.trans Ψ).symm (Ψ y) = Φ.symm y := by
  simp only [PartialDiffeomorph.symm_toPartialEquiv, PartialDiffeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.coe_trans_symm, Function.comp_apply]
  change (Φ.toPartialEquiv.symm : B → A) ((Ψ.toPartialEquiv.symm : C → B) (Ψ.toPartialEquiv y)) =
    (Φ.toPartialEquiv.symm : B → A) y
  have h2 : (Ψ.toPartialEquiv.symm : C → B) (Ψ.toPartialEquiv y) = y :=
    PartialEquiv.left_inv' Ψ.toPartialEquiv hy
  rw [h2]

end Composition

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M}

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_eq_symm_of_map_eq_trans {nk₀ nk₁ : StrongNeck S eps x t}
    {ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞} (h : nk₁.map = ψ.trans nk₀.map) :
    ∀ y ∈ nk₀.map.source, nk₁.map.symm (nk₀.map y) = ψ.symm y := by
  intro y hy
  rw [h, PartialDiffeomorph.trans_symm_apply ψ nk₀.map hy]

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_axial_fderiv_eq_of_map_eq_trans {nk₀ nk₁ : StrongNeck S eps x t}
    {ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞} (h : nk₁.map = ψ.trans nk₀.map)
    {z : Cylinder} (hz : z ∈ nk₀.map.source) :
    fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 =
      fderiv ℝ (fun a : ℝ => (ψ.symm (z.1, a)).2) z.2 1 := by
  have hev : (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) =ᶠ[𝓝 z.2]
      fun a : ℝ => (ψ.symm (z.1, a)).2 := by
    refine Filter.eventually_of_mem (U := {a : ℝ | (z.1, a) ∈ nk₀.map.source}) ?_ ?_
    · refine (nk₀.map.open_source.preimage ?_).mem_nhds ?_
      · exact Continuous.prodMk_right z.1
      · simpa using hz
    · intro a ha
      exact congrArg Prod.snd
        ((StrongNeck.transition_eq_symm_of_map_eq_trans h) (z.1, a) ha)
  rw [hev.fderiv_eq]

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_axial_fderiv_eq_neg_one_of_axialReflection
    {nk₀ nk₁ : StrongNeck S eps x t}
    (h : nk₁.map = cylinderAxialReflection.trans nk₀.map) {z : Cylinder}
    (hz : z ∈ nk₀.map.source) :
    fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 = -1 := by
  rw [StrongNeck.transition_axial_fderiv_eq_of_map_eq_trans h hz]
  have hfun : (fun a : ℝ => (cylinderAxialReflection.symm (z.1, a)).2) = fun a : ℝ => -a := by
    funext a
    rw [cylinderAxialReflection_symm_apply]
  rw [hfun]
  simp

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.not_transition_axial_fderiv_pos_of_axialReflection
    {nk₀ nk₁ : StrongNeck S eps x t}
    (h : nk₁.map = cylinderAxialReflection.trans nk₀.map) {z : Cylinder}
    (hz : z ∈ nk₀.map.source) :
    ¬ 0 < fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 := by
  rw [StrongNeck.transition_axial_fderiv_eq_neg_one_of_axialReflection h hz]
  norm_num

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_axial_fderiv_eq_one_of_map_eq_shift {nk₀ nk₁ : StrongNeck S eps x t}
    (c : ℝ) (h : nk₁.map = (cylinderAxialShift c).trans nk₀.map) {z : Cylinder}
    (hz : z ∈ nk₀.map.source) :
    fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 = 1 := by
  rw [StrongNeck.transition_axial_fderiv_eq_of_map_eq_trans h hz]
  exact cylinderAxialShift_symm_axial_fderiv c z

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.transition_axial_fderiv_pos_of_map_eq {nk₀ nk₁ : StrongNeck S eps x t}
    (h : nk₁.map = nk₀.map) {z : Cylinder} (hz : z ∈ nk₀.map.source) :
    0 < fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 := by
  have hz₁ : z ∈ nk₁.map.source := by rw [h]; exact hz
  have hev : (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) =ᶠ[𝓝 z.2] fun a : ℝ => a := by
    refine Filter.eventually_of_mem (U := {a : ℝ | (z.1, a) ∈ nk₁.map.source}) ?_ ?_
    · refine (nk₁.map.open_source.preimage ?_).mem_nhds ?_
      · exact Continuous.prodMk_right z.1
      · simpa using hz₁
    · intro a ha
      have h1 : nk₀.map (z.1, a) = nk₁.map (z.1, a) := by rw [h]
      change (nk₁.map.symm (nk₀.map (z.1, a))).2 = a
      rw [h1]
      exact congrArg Prod.snd (nk₁.map.left_inv' ha)
  rw [hev.fderiv_eq]
  simp

omit [T2Space M] [SigmaCompactSpace M] in
noncomputable def OrderedNeckChain.pairOfMapEq {eps t : ℝ} {x : M}
    (nk₀ nk₁ : StrongNeck S eps x t) (h : nk₁.map = nk₀.map) :
    OrderedNeckChain S eps t (nk₀.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) where
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
  transition_increasing := by
    intro i j hij z hz _
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
    exact StrongNeck.transition_axial_fderiv_pos_of_map_eq h (by simpa using hz)

omit [T2Space M] [SigmaCompactSpace M] in
theorem nonempty_orderedNeckChain_of_map_eq {eps t : ℝ} {x : M}
    (nk₀ nk₁ : StrongNeck S eps x t) (h : nk₁.map = nk₀.map) :
    Nonempty (OrderedNeckChain S eps t (nk₀.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))) :=
  ⟨OrderedNeckChain.pairOfMapEq nk₀ nk₁ h⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
