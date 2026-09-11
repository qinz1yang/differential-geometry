import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.EndomorphismFields


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
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
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
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
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance tangentEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x) (σ₁₂ := RingHom.id ℝ)

private local instance tangentEndomorphismNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) := inferInstance

private local instance tangentBilinearEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] TangentSpace I x)
    (σ₁₂ := RingHom.id ℝ)

private local instance tangentBilinearEndomorphismNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) := inferInstance

private local instance tensor0STotalSpaceTopology (s : ℕ) :
    TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem termSlotEndoCc_curry_apply (g : SmoothRiemannianMetric I M)
    (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (A : Tensor0SSpace (s + 1) I x) (u : TangentSpace I x) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term).toSection x) A)) u =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Term x) u) A := by
  rw [termSlotEndoCc_toSection]
  change (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
    (bilinearSlotInsertCLM (I := I) (M := M) s x (Term x) A)) u = _
  exact curry_termSlotFib_eq_slotInsert (I := I) (M := M) s x (Term x) A u

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_apply_section (g : SmoothRiemannianMetric I M)
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
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r
  let w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨W, hW⟩
  rw [tensorCovDerivAt_def (I := I) (M := M) g r q S x v]
  exact tensorRSCovariantDerivative_apply (I := I) (M := M) r q
    (LeviCivita (I := I) g) S.toSection w x v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_section_apply_add
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_curried_apply_section
    (g : SmoothRiemannianMetric I M) (r q : ℕ)
    (S : SmoothCcTensor g r (q + 1))
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) q x
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
        - (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) q x
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (q + 1) I x from
              S.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r
                (LeviCivita (I := I) g) W x v))) (Y x) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
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
  rw [hT, map_sub, sub_apply]
  rw [eq_sub_of_add_eq hCL.symm]

private def bilinEndoAppliedSection
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
  ⟨fun y : M => (Term y) (Y y),
    ContMDiff.clm_bundle_apply (b := id) Term.contMDiff Y.contMDiff⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem termSlotEndoCc_curriedSection_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) :
    (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I z from
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term).toSection z) (W z)) y (Y y)) =
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ]
        Tensor0SSpace (s + 1) I y from
        (endoSlotZeroCcTensor (I := I) (M := M) g s
          (bilinEndoAppliedSection (I := I) (M := M) Term Y)).toSection y) (W y)) := by
  funext y
  rw [Tensor0SNabla.curriedSection_apply, slotInsertEndoCc_toSection]
  exact termSlotEndoCc_curry_apply (I := I) (M := M) g s Term y (W y) (Y y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_termSlotEndoCc_curry_curve
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          ((endoCovariantDerivative (I := I) (M := M) g)
            (bilinEndoAppliedSection (I := I) (M := M) Term Y) x v) (W x)
        - slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
            ((Term x) ((LeviCivita (I := I) g) (fun y => Y y) x v)) (W x) := by
  have hbridge := termSlotEndoCc_curriedSection_eq (I := I) (M := M) g s Term W Y
  have hEndoSI := tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s
    (bilinEndoAppliedSection (I := I) (M := M) Term Y) x v
  set Lw : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g) W x v with hLw
  set NY : TangentSpace I x :=
    (LeviCivita (I := I) g) (fun y => Y y) x v with hNY
  have hT := tensorCovDerivAt_curried_apply_section (I := I) (M := M)
    g (s + 1) (s + 1) (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) W hW Y x v
  rw [hT, hbridge, ← hNY, ← hLw]
  have hSI := tensorCovDerivAt_section_apply_add (I := I) (M := M)
    g (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g s
        (bilinEndoAppliedSection (I := I) (M := M) Term Y)) W hW x v
  rw [hSI, hEndoSI, slotInsertEndoCc_toSection,
    Tensor0SNabla.curriedSection_apply,
    termSlotEndoCc_curry_apply (I := I) (M := M) g s Term x (W x) NY,
    termSlotEndoCc_curry_apply (I := I) (M := M) g s Term x Lw (Y x)]
  exact add_sub_sub_cancel_right
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Term Y) x v) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Term x) NY) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Term x) (Y x)) Lw)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_termSlotEndoCc_curry_apply_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x v) (Y x)) (W x) := by
  rw [tensorCovDerivAt_termSlotEndoCc_curry_curve (I := I) (M := M)
    g s Term W hW Y x v]
  rw [← sub_apply
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Term Y) x v))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((Term x) ((LeviCivita (I := I) g) (fun y => Y y) x v))) (W x)]
  rw [← slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
    ((endoCovariantDerivative (I := I) (M := M) g)
      (bilinEndoAppliedSection (I := I) (M := M) Term Y) x v)
    ((Term x) ((LeviCivita (I := I) g) (fun y => Y y) x v))]
  congr 1
  rw [bilinEndoCovariantDerivative_apply (I := I) (M := M) g Term Y x v]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem tensorCovDerivAt_termSlotEndoCc_curry_eq_slotInsertEndoFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) D)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x v) v0) D := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  rw [← hw, ← hY]
  exact tensorCovDerivAt_termSlotEndoCc_curry_apply_sections (I := I) (M := M)
    g s Term (fun y => w y) w.contMDiff Y x v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensorCovDerivAt_termSlotEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) =
      bilinearSlotInsertCLM (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1 + 1) x).injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.eval
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) D) m =
    Tensor0SSpace.eval
      (bilinearSlotInsertCLM (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x
          (show TangentSpace I x from v)) D) m
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [termSlotFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [tensorCovDerivAt_termSlotEndoCc_curry_eq_slotInsertEndoFib (I := I) (M := M) g s Term x v D
    (m 0)]
  simp only [Fin.cons_zero]
  rw [show Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)) = Matrix.vecTail m from by
    funext k; rfl]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covGrad_termSlotEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((bilinearSlotInsertCLM (I := I) (M := M) s x
            ((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1 + 1)
    (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term) x D v]
  rw [tensorCovDerivAt_termSlotEndoCc_eq (I := I) (M := M) g s Term x (v 0)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_eq_slotInsert_section
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) =
      connTermCc (I := I) g₀ g₁ + sharpTermCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((connTermCc (I := I) g₀ g₁ + sharpTermCc (I := I) g₀ g₁).toSection x) =
      (connTermCc (I := I) g₀ g₁).toSection x + (sharpTermCc (I := I) g₀ g₁).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      ((connTermCc (I := I) g₀ g₁).toSection x + (sharpTermCc (I := I) g₀ g₁).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connTermCc (I := I) g₀ g₁).toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (sharpTermCc (I := I) g₀ g₁).toSection x) D from rfl]
  change Tensor0SSpace.eval _ v = Tensor0SSpace.eval (_ + _) v
  rw [Tensor0SSpace.eval_add]
  have hcov := covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval
    (I := I) (M := M) g₀ g₁ x D v
  change Tensor0SSpace.eval _ v = Tensor0SSpace.eval _ (Matrix.vecTail v) at hcov
  rw [hcov]
  rw [connTermCc_toSection, sharpTermCc_toSection]
  change _ = Tensor0SSpace.eval
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connTermEndo (I := I) g₀ g₁ x) D) v +
    Tensor0SSpace.eval
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpTermEndo (I := I) g₀ g₁ x) D) v
  rw [termSlotFib_apply_eval, termSlotFib_apply_eval]
  rw [endoCov_eq_connTerm_add_sharpTerm (I := I) g₀ g₁ x (v 0)]
  rw [slotInsertEndoFib_add_left, add_apply,
    Tensor0SSpace.eval_add]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_succ_le_terms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (m + 1) (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (connTermCc (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (sharpTermCc (I := I) g₀ g₁)).toSection x) := by
  rw [← riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 2 2 m
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) x]
  rw [covGrad_inverseMetricDifferenceSlotCoefficient_eq_slotInsert_section (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 ((2 + 1) + m) x _ _

end Sobolev
end Analysis
end DifferentialGeometry

end
