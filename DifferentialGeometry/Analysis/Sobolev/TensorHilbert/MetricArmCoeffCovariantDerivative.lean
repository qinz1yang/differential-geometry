import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffFields
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance tangentEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x) (σ₁₂ := RingHom.id ℝ)

private local instance tangentBilinearEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] TangentSpace I x)
    (σ₁₂ := RingHom.id ℝ)

private local instance tensor0STotalSpaceTopology (s : ℕ) :
    TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem armSlotEndoCc_curry_apply (g : SmoothRiemannianMetric I M)
    (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (A : Tensor0SSpace (s + 1) I x) (u : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x) A)) u =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) u) A := by
  rw [armSlotEndoCc_toSection]
  change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
    (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) A)) u = _
  exact curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) A u

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotInsertEndoFib_sub_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ - Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ -
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) = ((-1 : ℝ)) • Λ₂ from by
    rw [neg_one_smul]]
  rw [slotInsertEndoFib_add_left (I := I) (M := M) s k x Λ₁ ((-1 : ℝ) • Λ₂)]
  rw [slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ₂]
  rw [neg_one_smul]

private theorem add_sub_sub_cancel_right {A : Type*} [AddCommGroup A]
    (a b c : A) : a + c - b - c = a - b := by
  abel

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_apply_section [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (r q : ℕ) (S : SmoothCcTensor g r q)
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (x : M) (v : E) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
        tensorCovDerivAt (I := I) (M := M) g r q S x v) (W x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
          (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace q I y from
            S.toSection y) (W y)) x v
        - (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
            S.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            W x v) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r
  let w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨W, hW⟩
  rw [tensorCovDerivAt_def (I := I) (M := M) g r q S x v]
  exact tensorRSCovariantDerivative_apply (I := I) (M := M) r q
    (LeviCivita (I := I) g) S.toSection w x v

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_section_apply_add [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r q : ℕ) (S : SmoothCcTensor g r q)
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (x : M) (v : E) :
    Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
        (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace q I y from
          S.toSection y) (W y)) x v =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
          tensorCovDerivAt (I := I) (M := M) g r q S x v) (W x)
        + (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
            S.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r
            (LeviCivita (I := I) g) W x v) := by
  have h := tensorCovDerivAt_apply_section (I := I) (M := M) g r q S W hW x v
  rw [eq_sub_iff_add_eq] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_curried_apply_section [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r q : ℕ)
    (S : SmoothCcTensor g r (q + 1))
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) q x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (q + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g r (q + 1) S x v) (W x))) (Y x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace (q + 1) I z from
              S.toSection z) (W z)) y (Y y)) x v
        - Tensor0SNabla.curriedSection I M
            (fun z : M => (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace (q + 1) I z from
              S.toSection z) (W z)) x
            ((LeviCivita (I := I) g) (fun y => Y y) x v)
        - (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) q x
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (q + 1) I x from
              S.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r
                (LeviCivita (I := I) g) W x v))) (Y x) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r
  let w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨W, hW⟩
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (q + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (q + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (q + 1) I z) y
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
          S.toSection y) (W y))) :=
    ContMDiff.clm_bundle_apply (b := id) S.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (q + 1)
      (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
        S.toSection y) (W y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hCL := tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (I := I) (M := M) g q
    (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
      S.toSection y) (W y)) (x := x) hU_at Y v
  have hT := tensorCovDerivAt_apply_section (I := I) (M := M) g r
    (q + 1) S W hW x v
  rw [hT, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL.symm]

private def bilinEndoAppliedSection [SigmaCompactSpace M]
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
  ⟨fun y : M => (Arm y) (Y y),
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff Y.contMDiff⟩

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  in
private theorem armSlotEndoCc_curriedSection_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) :
    (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I z from
          (armSlotEndoCc (I := I) (M := M) g s Arm).toSection z) (W z)) y (Y y)) =
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ]
        Tensor0SSpace (s + 1) I y from
        (endoSlotZeroCcTensor (I := I) (M := M) g s
          (bilinEndoAppliedSection (I := I) (M := M) Arm Y)).toSection y) (W y)) := by
  funext y
  rw [Tensor0SNabla.curriedSection_apply, slotInsertEndoCc_toSection]
  exact armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm y (W y) (Y y)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_curve
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          ((endoCovariantDerivative (I := I) (M := M) g)
            (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v) (W x)
        - slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
            ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v)) (W x) := by
  have hbridge := armSlotEndoCc_curriedSection_eq (I := I) (M := M) g s Arm W Y
  have hEndoSI := tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s
    (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v
  set Lw : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g) W x v with hLw
  set NY : TangentSpace I x :=
    (LeviCivita (I := I) g) (fun y => Y y) x v with hNY
  have hT := tensorCovDerivAt_curried_apply_section (I := I) (M := M)
    g (s + 1) (s + 1) (armSlotEndoCc (I := I) (M := M) g s Arm) W hW Y x v
  rw [hT, hbridge, ← hNY, ← hLw]
  have hSI := tensorCovDerivAt_section_apply_add (I := I) (M := M)
    g (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g s
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y)) W hW x v
  rw [hSI, hEndoSI, slotInsertEndoCc_toSection,
    Tensor0SNabla.curriedSection_apply,
    armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm x (W x) NY,
    armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm x Lw (Y x)]
  exact add_sub_sub_cancel_right
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_apply_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x)) (W x) := by
  rw [tensorCovDerivAt_armSlotEndoCc_curry_curve (I := I) (M := M)
    g s Arm W hW Y x v]
  rw [← ContinuousLinearMap.sub_apply
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v))) (W x)]
  rw [← slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
    ((endoCovariantDerivative (I := I) (M := M) g)
      (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v)
    ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v))]
  congr 1
  rw [bilinEndoCovariantDerivative_apply (I := I) (M := M) g Arm Y x v]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) v0) D := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  rw [← hw, ← hY]
  exact tensorCovDerivAt_armSlotEndoCc_curry_apply_sections (I := I) (M := M)
    g s Arm (fun y => w y) w.contMDiff Y x v

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_armSlotEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (armSlotEndoCc (I := I) (M := M) g s Arm) x v) =
      bilinearSlotInsertCLM (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [armSlotFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
        (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib (I := I) (M := M) g s Arm x v D
    (m 0)]
  simp only [Fin.cons_zero]
  rw [show Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)) = Matrix.vecTail m from by
    funext k; rfl]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_armSlotEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((bilinearSlotInsertCLM (I := I) (M := M) s x
            ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1 + 1)
    (armSlotEndoCc (I := I) (M := M) g s Arm) x D v]
  rw [tensorCovDerivAt_armSlotEndoCc_eq (I := I) (M := M) g s Arm x (v 0)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_eq_slotInsert_section
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁).toSection x) =
      (connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      ((connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connArmCc (I := I) g₀ g₁).toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (sharpArmCc (I := I) g₀ g₁).toSection x) D from rfl]
  change Tensor0SSpace.toModel _ v = Tensor0SSpace.toModel (_ + _) v
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [covGrad_gInvDiffSlotCoeff_toSection_eval (I := I) (M := M) g₀ g₁ x D v]
  rw [connArmCc_toSection, sharpArmCc_toSection]
  change _ = Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x) D) v +
    Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x) D) v
  rw [armSlotFib_apply_eval, armSlotFib_apply_eval]
  rw [endoCov_eq_connArm_add_sharpArm (I := I) g₀ g₁ x (v 0)]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_gInvDiffSlotCoeff_succ_le_arms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (m + 1) (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (connArmCc (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (sharpArmCc (I := I) g₀ g₁)).toSection x) := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 2 2 m
    (gInvDiffSlotCoeff (I := I) g₀ g₁) x]
  rw [covGrad_gInvDiffSlotCoeff_eq_slotInsert_section (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 ((2 + 1) + m) x _ _

end Sobolev
end Analysis
end DifferentialGeometry

end
