import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem threeArmJoint_const
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : SmoothCcTensor g r 2) {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun _ => A) (δ := δ) (δ' := δ') :=
  (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem threeArmJoint_add
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g r B
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA hB ⊢
  have h := joint_rs_add (I := I) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem threeArmJoint_sub
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g r B
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA hB ⊢
  have h := joint_rs_sub (I := I) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem threeArmJoint_smul
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (c : ℝ) (A : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => c • A s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA ⊢
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r 2
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r 2 ℝ E)
    (fun z : M => TensorRSSpace r 2 I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const
    (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (M := M × ℝ) (M' := ℝ) (n := ∞)
    (s := (Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (x := p₀) (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ
          metricPerturbationPathDomain (δ := δ) (δ' := δ')),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        (p := p₀))
        (e.open_baseSet.mem_nhds
          (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hp
    exact (e.linear ℝ hp).map_smul c ((A p.2).toSection p.1)
  · exact (e.linear ℝ
      (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
        c ((A p₀.2).toSection p₀.1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem threeArmJoint_comp
    (g : SmoothRiemannianMetric I M) {a b : ℕ}
    (A : ℝ → SmoothCcTensor g b 2) (B : SmoothCcTensor g a b)
    {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g b A
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g a
      (fun t => ccOperatorFieldComp (I := I) (M := M) g a b 2 (A t) B)
      (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA ⊢
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E)
    (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        (ccOperatorFieldComp (I := I) (M := M) g a b 2 (A p.2) B).toSection p.1))
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  have hBY₀ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          B.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) B.toSection.contMDiff Y.contMDiff
  have hBY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) p.1
        ((show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace b I p.1 from
          B.toSection p.1) (Y p.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    (hBY₀.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine happ.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) p.1 t) ?_
  rw [operatorFieldComposition_toSection]
  rfl

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end
