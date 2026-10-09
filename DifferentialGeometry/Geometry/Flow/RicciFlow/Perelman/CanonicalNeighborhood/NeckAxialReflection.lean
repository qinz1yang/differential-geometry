import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapChainTransition
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Pullback.CovariantDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness

local instance : IsManifold IC ((∞ : WithTop ℕ∞) + 1) Cylinder :=
  by simpa using (inferInstance : IsManifold IC (∞ : WithTop ℕ∞) Cylinder)

def cylinderAxialReflectionIsometry : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder where
  toFun := (cylinderAxialReflection : Cylinder → Cylinder)
  invFun := (cylinderAxialReflection.symm : Cylinder → Cylinder)
  left_inv y := cylinderAxialReflection.left_inv' (mem_univ y)
  right_inv y := cylinderAxialReflection.right_inv' (mem_univ y)
  contMDiff_toFun := by
    have h : ContMDiffOn IC IC ∞ (cylinderAxialReflection : Cylinder → Cylinder) Set.univ :=
      cylinderAxialReflection.contMDiffOn_toFun
    exact contMDiffOn_univ.mp h
  contMDiff_invFun := by
    have h : ContMDiffOn IC IC ∞ (cylinderAxialReflection.symm : Cylinder → Cylinder) Set.univ :=
      cylinderAxialReflection.symm.contMDiffOn_toFun
    exact contMDiffOn_univ.mp h

theorem cylinderAxialReflectionIsometry_apply (y : Cylinder) :
    cylinderAxialReflectionIsometry y = (y.1, -y.2) := rfl

theorem cylinderAxialReflectionIsometry_coe :
    (cylinderAxialReflectionIsometry : Cylinder → Cylinder) =
      (cylinderAxialReflection : Cylinder → Cylinder) := rfl

theorem cylinderAxialReflectionIsometry_eq_diffeomorph :
    (cylinderAxialReflectionIsometry : Cylinder → Cylinder) =
      (DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) 0 (-1)
        (by norm_num) : Cylinder → Cylinder) := by
  rw [cylinderAxialReflectionIsometry_coe]
  funext y
  simp

theorem cylinderAxialReflection_mfderiv (y : Cylinder) (v : TangentSpace IC y) :
    mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v =
      cylinderAxialReflectionTangent y v := by
  have hcoe : (cylinderAxialReflection : Cylinder → Cylinder) =
      (DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) 0 (-1)
        (by norm_num) : Cylinder → Cylinder) :=
    cylinderAxialReflectionIsometry_eq_diffeomorph
  rw [hcoe, DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph_mfderiv]
  change (v.1, (-1 : ℝ) * v.2) = (v.1, -v.2)
  simp

theorem tensor02CovDerivNormWith_axialReflection (a : ℕ)
    (A : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2)
    (g : SmoothRiemannianMetric IC Cylinder)
    (hg : ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
      g.inner (cylinderAxialReflection y)
        (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
        (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y w) =
          g.inner y v w)
    (y : Cylinder) :
    tensor02CovDerivNormWith a (pullbackTensor02FieldCross cylinderAxialReflectionIsometry A)
        g g y =
      tensor02CovDerivNormWith a A g g (cylinderAxialReflection y) := by
  have hδ : ∀ x ∈ (⊤ : Set Cylinder), ∀ v : Fin 2 → TangentSpace IC x,
      pullbackTensor02FieldCross cylinderAxialReflectionIsometry A x v =
        A (cylinderAxialReflection x)
          (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) x (v q)) := by
    intro x _ v
    rw [pullbackTensor02FieldCross_apply, cylinderAxialReflectionIsometry_coe]
  have hG : ∀ x ∈ (⊤ : Set Cylinder), ∀ v w : TangentSpace IC x,
      g.inner x v w =
        g.inner (cylinderAxialReflection x)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) x v)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) x w) := by
    intro x _ v w
    exact (hg x v w).symm
  exact tensor02_cov_deriv_norm_with_eq_of_partial_diffeomorph (Φ := cylinderAxialReflection)
    (V := ⊤) (fun _ _ => trivial) g A
    (pullbackTensor02FieldCross cylinderAxialReflectionIsometry A) g hδ hG a y trivial

theorem CylinderReference.covDerivNormWith_axialReflection (h : CylinderReference)
    (a : ℕ) (A : Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2) {s : ℝ} (hs : s ≤ 0)
    (y : Cylinder) :
    tensor02CovDerivNormWith a (pullbackTensor02FieldCross cylinderAxialReflectionIsometry A)
        (h.metric s) (h.metric s) y =
      tensor02CovDerivNormWith a A (h.metric s) (h.metric s) (cylinderAxialReflection y) :=
  tensor02CovDerivNormWith_axialReflection a A (h.metric s)
    (fun y v w => by
      rw [cylinderAxialReflection_mfderiv, cylinderAxialReflection_mfderiv]
      exact CylinderReference.inner_axialReflection h hs y v w) y

private noncomputable def axialReflectionCorrection
    (h : ℝ → SmoothRiemannianMetric IC Cylinder) (s : ℝ) :
    Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 :=
  pullbackTensor02FieldCross cylinderAxialReflectionIsometry (metricTensorField (I := IC) (h s)) -
    metricTensorField (I := IC) (h s)

private theorem axialReflectionCorrection_apply
    (h : ℝ → SmoothRiemannianMetric IC Cylinder) (s : ℝ) (y : Cylinder)
    (v : Fin 2 → TangentSpace IC y) :
    axialReflectionCorrection h s y v =
      pullbackTensor02FieldCross cylinderAxialReflectionIsometry
          (metricTensorField (I := IC) (h s)) y v -
        metricTensorField (I := IC) (h s) y v := by
  rw [axialReflectionCorrection, ContMDiffSection.coe_sub, Pi.sub_apply,
    Tensor0SSpace.sub_apply]

private theorem axialReflectionCorrection_apply_eq_zero
    (h : ℝ → SmoothRiemannianMetric IC Cylinder) {s : ℝ}
    (hiso : ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
      (h s).inner (cylinderAxialReflection y)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y w) =
        (h s).inner y v w)
    (y : Cylinder) (v : Fin 2 → TangentSpace IC y) :
    axialReflectionCorrection h s y v = 0 := by
  rw [axialReflectionCorrection_apply, pullbackTensor02FieldCross_apply,
    metricTensorField_apply, metricTensorField_apply, cylinderAxialReflectionIsometry_coe,
    hiso y (v 0) (v 1), sub_self]

private theorem axialReflectionCorrection_eq_zero
    (h : ℝ → SmoothRiemannianMetric IC Cylinder) {s : ℝ}
    (hiso : ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
      (h s).inner (cylinderAxialReflection y)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y w) =
        (h s).inner y v w) :
    axialReflectionCorrection h s = 0 := by
  apply ContMDiffSection.ext
  intro y
  apply tensor0SSpace_ext (I := IC) 2 y
  intro v
  exact axialReflectionCorrection_apply_eq_zero h hiso y v

section Reflection

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

noncomputable def axialReflectionMetricComparison
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : Cylinder → M} {U : Set Cylinder}
    {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (hiso : ∀ s ∈ times, ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
      (h s).inner (cylinderAxialReflection y)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y w) =
        (h s).inner y v w)
    (hU : ∀ y ∈ U, cylinderAxialReflection y ∈ U)
    (hF : ∀ y ∈ U, MDifferentiableAt IC I3 F (cylinderAxialReflection y))
    (C : MetricComparisonOn h g F U times order eps) :
    MetricComparisonOn h g (fun y => F (cylinderAxialReflection y)) U times order eps := by
  let PB : ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 :=
    fun s => pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.pullback s)
  let JT : ℕ → ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 :=
    fun b s => pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.jet b s) +
      axialReflectionCorrection h s
  have hPB : ∀ (s : ℝ) (y : Cylinder) (v : Fin 2 → TangentSpace IC y),
      PB s y v = C.pullback s (cylinderAxialReflection y)
        (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v q)) := by
    intro s y v
    change pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.pullback s) y v = _
    rw [pullbackTensor02FieldCross_apply, cylinderAxialReflectionIsometry_coe]
  have hJT : ∀ (b : ℕ) (s : ℝ) (y : Cylinder) (v : Fin 2 → TangentSpace IC y),
      JT b s y v = C.jet b s (cylinderAxialReflection y)
          (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v q)) +
        axialReflectionCorrection h s y v := by
    intro b s y v
    change (pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.jet b s) +
      axialReflectionCorrection h s) y v = _
    rw [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
      pullbackTensor02FieldCross_apply, cylinderAxialReflectionIsometry_coe]
  refine
    { pullback := PB
      pullback_eq := ?_
      jet := JT
      jet_zero := ?_
      jet_succ := ?_
      equivalence := ?_
      close := ?_ }
  · intro s y hy v
    rw [hPB s y v, C.pullback_eq s (cylinderAxialReflection y) (hU y hy)
      (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v q))]
    have hchain : ∀ j : Fin 2,
        mfderiv IC I3 (fun z : Cylinder => F (cylinderAxialReflection z)) y (v j) =
          mfderiv IC I3 F (cylinderAxialReflection y)
            (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v j)) := by
      have hcomp : (fun z : Cylinder => F (cylinderAxialReflection z)) =
          (F ∘ (cylinderAxialReflection : Cylinder → Cylinder)) := rfl
      intro j
      rw [hcomp, mfderiv_comp_apply y (hF y hy)
          (cylinderAxialReflection.mdifferentiableAt (by decide) (mem_univ y)) (v j)]
    rw [hchain 0, hchain 1]
  · intro s y v
    rw [hJT 0 s y v, C.jet_zero s (cylinderAxialReflection y)
        (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v q)),
      hPB s y v, axialReflectionCorrection_apply, pullbackTensor02FieldCross_apply,
      metricTensorField_apply, metricTensorField_apply, cylinderAxialReflectionIsometry_coe]
    ring
  · intro b s hs y hy v
    rw [hJT (b + 1) s y v, C.jet_succ b s hs (cylinderAxialReflection y) (hU y hy)
        (fun q => mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y (v q)),
      axialReflectionCorrection_apply_eq_zero h (hiso s hs) y v, add_zero]
    refine (derivWithin_congr ?_ ?_).symm
    · intro a ha
      dsimp only
      rw [hJT b a y v, axialReflectionCorrection_apply_eq_zero h (hiso a ha) y v, add_zero]
    · rw [hJT b s y v, axialReflectionCorrection_apply_eq_zero h (hiso s hs) y v, add_zero]
  · intro s hs y hy v
    obtain ⟨h1, h2⟩ := C.equivalence s hs (cylinderAxialReflection y) (hU y hy)
      (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
    rw [hiso s hs y v v] at h1 h2
    rw [hPB s y (fun _ => v)]
    exact ⟨h1, h2⟩
  · intro a b hab s hs y hy
    have hzero : JT b s =
        pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.jet b s) := by
      change pullbackTensor02FieldCross cylinderAxialReflectionIsometry (C.jet b s) +
        axialReflectionCorrection h s = _
      rw [axialReflectionCorrection_eq_zero h (hiso s hs), add_zero]
    rw [hzero, tensor02CovDerivNormWith_axialReflection a (C.jet b s) (h s) (hiso s hs) y]
    exact C.close a b hab s hs (cylinderAxialReflection y) (hU y hy)

end Reflection

section NeckReflection

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M}

noncomputable def StrongNeck.axialReflection (nk : StrongNeck S eps x t) :
    StrongNeck S eps x t := by
  have hU : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹,
      cylinderAxialReflection y ∈ Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ := by
    intro y hy
    refine ⟨trivial, ?_⟩
    have h2 : y.2 ∈ Set.Ioo (-eps⁻¹) eps⁻¹ := hy.2
    simp only [cylinderAxialReflection_apply, Set.mem_Ioo] at *
    exact ⟨by linarith [h2.2], by linarith [h2.1]⟩
  have hF : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹,
      MDifferentiableAt IC I3 (nk.map : Cylinder → M) (cylinderAxialReflection y) :=
    fun y hy => nk.map.mdifferentiableAt (by decide) (nk.domain (hU y hy))
  have hiso : ∀ s ∈ Set.Icc (-1 : ℝ) 0, ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
      (nk.cylinder.metric s).inner (cylinderAxialReflection y)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y v)
          (mfderiv IC IC (cylinderAxialReflection : Cylinder → Cylinder) y w) =
        (nk.cylinder.metric s).inner y v w := fun s hs y v w => by
    rw [cylinderAxialReflection_mfderiv, cylinderAxialReflection_mfderiv]
    exact CylinderReference.inner_axialReflection nk.cylinder hs.2 y v w
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := nk.Q_pos
      cylinder := nk.cylinder
      map := cylinderAxialReflection.trans nk.map
      center := nk.center
      center_eq := ?_
      domain := ?_
      time_domain := nk.time_domain
      comparison := ?_ }
  · change nk.map (cylinderAxialReflection (nk.center, 0)) = x
    rw [cylinderAxialReflection_apply]
    simpa using nk.center_eq
  · intro y hy
    exact ⟨mem_univ y, nk.domain (hU y hy)⟩
  · exact axialReflectionMetricComparison hiso hU hF nk.comparison

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.axialReflection_map (nk : StrongNeck S eps x t) :
    nk.axialReflection.map = cylinderAxialReflection.trans nk.map := rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.axialReflection_transition_axial_fderiv (nk : StrongNeck S eps x t) :
    fderiv ℝ (fun a : ℝ => (nk.axialReflection.map.symm (nk.map (nk.center, a))).2) 0 1 =
      -1 := by
  have hz : (nk.center, (0 : ℝ)) ∈ nk.map.source := by
    refine nk.domain ⟨trivial, ?_⟩
    have hpos : (0 : ℝ) < eps⁻¹ := inv_pos.mpr nk.eps_pos
    exact ⟨by linarith, by linarith⟩
  exact StrongNeck.transition_axial_fderiv_eq_neg_one_of_axialReflection (nk₀ := nk)
    (nk₁ := nk.axialReflection) rfl hz

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.not_forall_transition_axial_fderiv_pos (nk : StrongNeck S eps x t) :
    ¬ (∀ (nk₀ nk₁ : StrongNeck S eps x t), ∀ z ∈ nk₀.map.source,
        nk₀.map z ∈ nk₁.map.target →
          0 < fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1) := by
  intro h
  have hz : (nk.center, (0 : ℝ)) ∈ nk.map.source := by
    refine nk.domain ⟨trivial, ?_⟩
    have hpos : (0 : ℝ) < eps⁻¹ := inv_pos.mpr nk.eps_pos
    exact ⟨by linarith, by linarith⟩
  have hzt : nk.map (nk.center, 0) ∈ nk.axialReflection.map.target := by
    change nk.map (nk.center, 0) ∈ (cylinderAxialReflection.trans nk.map).target
    rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_target]
    exact ⟨nk.map.map_source' hz, mem_univ _⟩
  exact (StrongNeck.not_transition_axial_fderiv_pos_of_axialReflection (nk₀ := nk)
    (nk₁ := nk.axialReflection) rfl hz)
    (h nk nk.axialReflection (nk.center, 0) hz hzt)

end NeckReflection

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
