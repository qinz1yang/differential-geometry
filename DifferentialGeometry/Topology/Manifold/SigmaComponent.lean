import DifferentialGeometry.Topology.Manifold.ConnectedComponent
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma
import DifferentialGeometry.Topology.Manifold.SigmaOrientation
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v
variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (M : ι → Type u) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

omit [Nonempty H] [∀ i, IsManifold I ∞ (M i)] in
private theorem sigmaMk_mem_component (i : ι) (x : M i)
    (y : DifferentialGeometry.connectedComponentOpen (I := I) x) :
    (⟨i, y.val⟩ : Σ j, M j) ∈ connectedComponent (⟨i, x⟩ : Σ j, M j) := by
  have h : ConnectedComponents.mk y.val = ConnectedComponents.mk x :=
    ConnectedComponents.coe_eq_coe'.mpr y.property
  exact ConnectedComponents.coe_eq_coe'.mp (by
    simpa only [Continuous.connectedComponentsMap_mk] using
      congrArg (continuous_sigmaMk (i := i) (σ := M)).connectedComponentsMap h)

omit [∀ i, IsManifold I ∞ (M i)] in
private theorem sigma_fst_eq_of_mem_component (i : ι) (x : M i)
    (y : DifferentialGeometry.connectedComponentOpen (I := I) (⟨i, x⟩ : Σ j, M j)) :
    y.val.fst = i := by
  have hf : IsLocallyConstant (Sigma.fst : (Σ j, M j) → ι) := isOpen_sigma_fst_preimage
  exact hf.apply_eq_of_isPreconnected isPreconnected_connectedComponent
    y.property mem_connectedComponent

omit [∀ i, IsManifold I ∞ (M i)] in
private theorem sigmaMk_component_surjective (i : ι) (x : M i) :
    Surjective (fun y : DifferentialGeometry.connectedComponentOpen (I := I) x =>
      (⟨⟨i, y.val⟩, sigmaMk_mem_component M i x y⟩ :
        DifferentialGeometry.connectedComponentOpen (I := I) (⟨i, x⟩ : Σ j, M j))) := by
  classical
  intro y
  have hi := sigma_fst_eq_of_mem_component M i x y
  obtain ⟨⟨j, z⟩, hz⟩ := y
  dsimp at hi
  subst j
  let r : (Σ j, M j) → M i := fun p => if h : p.fst = i then h ▸ p.snd else x
  have hr : Continuous r := by
    apply continuous_sigma
    intro j
    by_cases h : j = i
    · subst j
      simp only [r, dite_eq_left rfl]
      exact continuous_id
    · simp only [r, dite_eq_right h]
      exact continuous_const
  have hrmk (w : M i) : r ⟨i, w⟩ = w := by simp [r]
  have hz' : z ∈ connectedComponent x := by
    have h := ConnectedComponents.coe_eq_coe'.mpr hz
    have h' := congrArg hr.connectedComponentsMap h
    simp only [Continuous.connectedComponentsMap_mk, hrmk] at h'
    exact ConnectedComponents.coe_eq_coe'.mp h'
  exact ⟨⟨z, hz'⟩, rfl⟩

def sigmaComponentDiffeomorph (i : ι) (x : M i) :
    Diffeomorph I I (DifferentialGeometry.connectedComponentOpen (I := I) x)
      (DifferentialGeometry.connectedComponentOpen (I := I) (⟨i, x⟩ : Σ j, M j)) ∞ := by
  let f := fun y : DifferentialGeometry.connectedComponentOpen (I := I) x =>
    (⟨⟨i, y.val⟩, sigmaMk_mem_component M i x y⟩ :
      DifferentialGeometry.connectedComponentOpen (I := I) (⟨i, x⟩ : Σ j, M j))
  have hf : IsLocalDiffeomorph I I ∞ f := by
    intro y
    apply DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    exact ((DifferentialGeometry.isLocalDiffeomorph_subtype_val _ y).comp I (Σ j, M j)
      (isLocalDiffeomorph_sigmaMk (I := I) (M := M) i y.val))
  have hi : Injective f := by
    intro y z h
    apply Subtype.ext
    exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  exact hf.diffeomorphOfBijective ⟨hi, sigmaMk_component_surjective M i x⟩

@[simp] theorem sigmaComponentDiffeomorph_apply (i : ι) (x : M i)
    (y : DifferentialGeometry.connectedComponentOpen (I := I) x) :
    (sigmaComponentDiffeomorph M i x y).val = ⟨i, y.val⟩ := rfl

variable [FiniteDimensional ℝ E] {n : ℕ}

theorem sigmaComponentDiffeomorph_preservesOrientation
    (hdim : Module.finrank ℝ E = n) (o : ∀ i, ManifoldOrientation I (M i) n)
    (i : ι) (x : M i) :
    (sigmaComponentDiffeomorph M i x).preservesOrientation
      ((o i).restrictOpen (DifferentialGeometry.connectedComponentOpen (I := I) x))
      ((manifoldOrientationUnion hdim o).restrictOpen
        (DifferentialGeometry.connectedComponentOpen (I := I) (⟨i, x⟩ : Σ j, M j))) := by
  intro y
  have hder : mfderiv I I (sigmaComponentDiffeomorph M i x) y = ContinuousLinearMap.id ℝ E := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := I)]
    change mfderiv I I (fun z : DifferentialGeometry.connectedComponentOpen (I := I) x =>
      (⟨i, z.val⟩ : Σ j, M j)) y = _
    rw [DifferentialGeometry.mfderiv_restrict_open (I := I) (J := I)]
    exact mfderiv_sigmaMk i y.val
  have he : ((sigmaComponentDiffeomorph M i x).mfderivToContinuousLinearEquiv
      (by simp) y).toLinearEquiv = LinearEquiv.refl ℝ E := by
    ext v
    exact congrArg (fun L : E →L[ℝ] E => L v) hder
  rw [he]
  change Orientation.map (Fin n) (LinearEquiv.refl ℝ E) ((o i).orientation y.val) =
    (o i).orientation y.val
  simp only [Orientation.map_refl]
  rfl

end DifferentialGeometry.Topology
