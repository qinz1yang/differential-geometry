import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapChainCoOrientation

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section FiberPreserving

variable {Ψ Φ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}

theorem CylinderFiberPreserving.eq_fst_of_fst_eq (h : CylinderFiberPreserving Ψ) {z z' : Cylinder}
    (hz : z.1 = z'.1) : (Ψ z).1 = (Ψ z').1 := by
  have hzz : z' = (z.1, z'.2) := by rw [hz]
  rw [hzz, ← h z z'.2]

theorem cylinderIdentity_fiberPreserving : CylinderFiberPreserving cylinderIdentity := fun _ _ => rfl

theorem cylinderAxialShift_fiberPreserving (c : ℝ) :
    CylinderFiberPreserving (cylinderAxialShift c) :=
  (cylinderAxialShift_cooriented c).1

theorem cylinderAxialReflection_isometry_fiberPreserving :
    CylinderFiberPreserving cylinderAxialReflection := cylinderAxialReflection_fiberPreserving

theorem CylinderFiberPreserving.trans (hΦ : CylinderFiberPreserving Φ)
    (hΨ : CylinderFiberPreserving Ψ) : CylinderFiberPreserving (Φ.trans Ψ) := by
  intro y a
  have h1 : (Φ.trans Ψ) (y.1, a) = Ψ (Φ (y.1, a)) := rfl
  have h2 : (Φ.trans Ψ) y = Ψ (Φ y) := rfl
  rw [h1, h2]
  exact hΨ.eq_fst_of_fst_eq (hΦ y a)

end FiberPreserving

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

theorem PartialDiffeomorph.trans_source (Φ : PartialDiffeomorph J₁ J₂ A B ∞)
    (Ψ : PartialDiffeomorph J₂ J₃ B C ∞) :
    (Φ.trans Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source := by
  rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_source]
  rfl

theorem PartialDiffeomorph.trans_apply (Φ : PartialDiffeomorph J₁ J₂ A B ∞)
    (Ψ : PartialDiffeomorph J₂ J₃ B C ∞) (z : A) : (Φ.trans Ψ) z = Ψ (Φ z) := rfl

theorem PartialDiffeomorph.symm_symm (Φ : PartialDiffeomorph J₁ J₂ A B ∞) :
    Φ.symm.symm = Φ := by
  apply PartialDiffeomorph.eq_of_toPartialEquiv_eq
  rw [PartialDiffeomorph.symm_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
    PartialEquiv.symm_symm]

end Composition

section AxialNonvanishing

theorem CylinderFiberPreserving.axial_fderiv_ne_zero {Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}
    (h : CylinderFiberPreserving Ψ) {y : Cylinder} (hy : y ∈ Ψ.source) :
    fderiv ℝ (fun a : ℝ => (Ψ (y.1, a)).2) y.2 1 ≠ 0 := by
  have hmem : Ψ y ∈ Ψ.target := Ψ.map_source' hy
  have hψ : ContMDiffAt IC IC ∞ (Ψ : Cylinder → Cylinder) y :=
    Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hy)
  have hψs : ContMDiffAt IC IC ∞ (Ψ.symm : Cylinder → Cylinder) (Ψ y) :=
    Ψ.symm.contMDiffOn_toFun.contMDiffAt (Ψ.open_target.mem_nhds hmem)
  have hv : DifferentiableAt ℝ (fun a : ℝ => (Ψ (y.1, a)).2) y.2 := by
    have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun a : ℝ => (y.1, a)) y.2 :=
      (contMDiffAt_const (c := y.1)).prodMk contMDiffAt_id
    exact (((hψ.comp y.2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
  have hβ : DifferentiableAt ℝ (fun t : ℝ => (Ψ.symm ((Ψ y).1, t)).2) (Ψ y).2 := by
    have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun t : ℝ => ((Ψ y).1, t)) (Ψ y).2 :=
      (contMDiffAt_const (c := (Ψ y).1)).prodMk contMDiffAt_id
    exact (((hψs.comp (Ψ y).2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
  have hcomp : ((fun t : ℝ => (Ψ.symm ((Ψ y).1, t)).2) ∘
      (fun a : ℝ => (Ψ (y.1, a)).2)) =ᶠ[𝓝 y.2] fun a : ℝ => a := by
    have hpre : {a : ℝ | (y.1, a) ∈ Ψ.source} ∈ 𝓝 y.2 :=
      (Ψ.open_source.preimage (Continuous.prodMk_right y.1)).mem_nhds (by simpa using hy)
    refine Filter.eventually_of_mem hpre fun a ha => ?_
    have h1 : Ψ (y.1, a) = ((Ψ y).1, (Ψ (y.1, a)).2) := Prod.ext (h y a) rfl
    have h2 : Ψ.symm (Ψ (y.1, a)) = (y.1, a) := Ψ.left_inv' ha
    rw [Function.comp_apply, h1.symm, h2]
  have hchain := fderiv_comp y.2 hβ hv
  have hkey : (fderiv ℝ ((fun t : ℝ => (Ψ.symm ((Ψ y).1, t)).2) ∘
      (fun a : ℝ => (Ψ (y.1, a)).2)) y.2) 1 = 1 := by
    rw [hcomp.fderiv_eq]
    simp
  rw [hchain, ContinuousLinearMap.comp_apply] at hkey
  intro hzero
  rw [hzero, map_zero] at hkey
  exact one_ne_zero hkey.symm

end AxialNonvanishing

section ReflectionObstruction

theorem not_cylinderCoOriented_of_eventuallyEq_axialReflection
    {Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞} {y : Cylinder} (hy : y ∈ Ψ.source)
    (h : ∀ᶠ a in 𝓝 y.2, Ψ (y.1, a) = cylinderAxialReflection (y.1, a)) :
    ¬ CylinderCoOriented Ψ := by
  intro hco
  have hpos := hco.2.2 y hy
  have hev : (fun a : ℝ => (Ψ (y.1, a)).2) =ᶠ[𝓝 y.2] fun a : ℝ => -a := by
    refine Filter.eventually_of_mem h fun a ha => ?_
    have ha' : Ψ (y.1, a) = cylinderAxialReflection (y.1, a) := ha
    simp only [ha', cylinderAxialReflection_apply]
  rw [hev.fderiv_eq] at hpos
  have hval : (fderiv ℝ (fun a : ℝ => -a) y.2) 1 = -1 := by simp
  rw [hval] at hpos
  norm_num at hpos

end ReflectionObstruction

section CoOrientedClosure

variable {Φ Ψ : PartialDiffeomorph IC IC Cylinder Cylinder ∞}

theorem CylinderCoOriented.symm (h : CylinderCoOriented Ψ) : CylinderCoOriented Ψ.symm := by
  refine ⟨h.2.1, ?_, ?_⟩
  · rw [PartialDiffeomorph.symm_symm]
    exact h.1
  · intro z hz
    exact CylinderCoOriented.axial_fderiv_symm_pos h hz

theorem CylinderCoOriented.trans (hΦ : CylinderCoOriented Φ) (hΨ : CylinderCoOriented Ψ) :
    CylinderCoOriented (Φ.trans Ψ) := by
  refine ⟨hΦ.1.trans hΨ.1, ?_, ?_⟩
  · intro y a
    have hcoe : ((Φ.trans Ψ).symm : Cylinder → Cylinder) =
        (Φ.symm : Cylinder → Cylinder) ∘ (Ψ.symm : Cylinder → Cylinder) := by
      funext z
      have h1 : (Φ.trans Ψ).symm.toPartialEquiv =
          (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).symm := by
        rw [PartialDiffeomorph.symm_toPartialEquiv, PartialDiffeomorph.trans_toPartialEquiv,
          OpenPartialHomeomorph.trans_toPartialEquiv]
        rfl
      rw [show ((Φ.trans Ψ).symm : Cylinder → Cylinder) z =
          (Φ.trans Ψ).symm.toPartialEquiv.toFun z from rfl, h1, PartialEquiv.coe_trans_symm,
        Function.comp_apply]
      rfl
    have h1 : (Ψ.symm (y.1, a)).1 = (Ψ.symm y).1 := hΨ.2.1 y a
    have h2 : (Φ.symm (Ψ.symm (y.1, a))).1 = (Φ.symm (Ψ.symm y)).1 :=
      hΦ.2.1.eq_fst_of_fst_eq h1
    rw [hcoe]
    exact h2
  · intro y hy
    rw [PartialDiffeomorph.trans_source] at hy
    obtain ⟨hyΦ, hyΨ⟩ := hy
    have hβ : DifferentiableAt ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2 := by
      have hΦdiff : ContMDiffAt IC IC ∞ (Φ : Cylinder → Cylinder) y :=
        Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hyΦ)
      have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun a : ℝ => (y.1, a)) y.2 :=
        (contMDiffAt_const (c := y.1)).prodMk contMDiffAt_id
      exact (((hΦdiff.comp y.2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
    have hγ : DifferentiableAt ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2) := by
      have hΨdiff : ContMDiffAt IC IC ∞ (Ψ : Cylinder → Cylinder) (Φ y) :=
        Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hyΨ)
      have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) IC ∞ (fun t : ℝ => ((Φ y).1, t)) ((Φ y).2) :=
        (contMDiffAt_const (c := (Φ y).1)).prodMk contMDiffAt_id
      exact (((hΨdiff.comp (Φ y).2 hcurve).snd).mdifferentiableAt (by simp)).differentiableAt
    have hcomp : (fun a : ℝ => (Ψ (Φ (y.1, a))).2) =ᶠ[𝓝 y.2]
        ((fun t : ℝ => (Ψ ((Φ y).1, t)).2) ∘ (fun a : ℝ => (Φ (y.1, a)).2)) := by
      filter_upwards with a
      simp only [Function.comp_apply]
      have h1 : Φ (y.1, a) = ((Φ y).1, (Φ (y.1, a)).2) := Prod.ext (hΦ.1 y a) rfl
      rw [h1]
    have hchain := fderiv_comp y.2 hγ hβ
    have hval : (fderiv ℝ (fun a : ℝ => (Ψ (Φ (y.1, a))).2) y.2) 1 =
        (fderiv ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2))
          ((fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1) := by
      rw [hcomp.fderiv_eq, hchain, ContinuousLinearMap.comp_apply]
    have hβpos : 0 < (fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1 := hΦ.2.2 y hyΦ
    have hγpos : 0 < (fderiv ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2)) 1 :=
      hΨ.2.2 (Φ y) hyΨ
    have hmul : (fderiv ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2))
        ((fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1) =
        ((fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1) *
          ((fderiv ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2)) 1) := by
      conv_lhs => rw [show (fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1 =
        ((fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1) • (1 : ℝ) by simp]
      rw [map_smul, smul_eq_mul]
    have hgoal : (fderiv ℝ (fun a : ℝ => (Ψ (Φ (y.1, a))).2) y.2) 1 =
        ((fderiv ℝ (fun a : ℝ => (Φ (y.1, a)).2) y.2) 1) *
          ((fderiv ℝ (fun t : ℝ => (Ψ ((Φ y).1, t)).2) ((Φ y).2)) 1) := by
      rw [hval, hmul]
    change 0 < (fderiv ℝ (fun a : ℝ => (Ψ (Φ (y.1, a))).2) y.2) 1
    rw [hgoal]
    exact mul_pos hβpos hγpos

end CoOrientedClosure

section Distinctness

theorem cylinderAxialShift_ne_cylinderAxialShift {c d : ℝ} (hcd : c ≠ d) :
    cylinderAxialShift c ≠ cylinderAxialShift d := by
  intro h
  have hfun : (cylinderAxialShift c : Cylinder → Cylinder) =
      (cylinderAxialShift d : Cylinder → Cylinder) :=
    congrArg (fun Φ : PartialDiffeomorph IC IC Cylinder Cylinder ∞ => (Φ : Cylinder → Cylinder)) h
  obtain ⟨y⟩ : Nonempty Cylinder :=
    ⟨(⟨EuclideanSpace.single 0 1, by simp [Sphere]⟩, 0)⟩
  have hy := congrFun hfun y
  have h2 : y.2 + c = y.2 + d := by
    have := congrArg Prod.snd hy
    simpa [cylinderAxialShift] using this
  exact hcd (by linarith)

theorem cylinderIdentity_ne_cylinderAxialShift {c : ℝ} (hc : c ≠ 0) :
    (cylinderIdentity : PartialDiffeomorph IC IC Cylinder Cylinder ∞) ≠ cylinderAxialShift c := by
  intro h
  have hfun : (cylinderIdentity : Cylinder → Cylinder) =
      (cylinderAxialShift c : Cylinder → Cylinder) :=
    congrArg (fun Φ : PartialDiffeomorph IC IC Cylinder Cylinder ∞ => (Φ : Cylinder → Cylinder)) h
  obtain ⟨y⟩ : Nonempty Cylinder :=
    ⟨(⟨EuclideanSpace.single 0 1, by simp [Sphere]⟩, 0)⟩
  have hy := congrFun hfun y
  have h2 : y.2 + c = y.2 := by
    have := congrArg Prod.snd hy
    simpa [cylinderIdentity, cylinderAxialShift] using this
  exact hc (by linarith)

theorem cylinderAxialShift_trans_cooriented (c d : ℝ) :
    CylinderCoOriented ((cylinderAxialShift c).trans (cylinderAxialShift d)) :=
  (cylinderAxialShift_cooriented c).trans (cylinderAxialShift_cooriented d)

end Distinctness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
