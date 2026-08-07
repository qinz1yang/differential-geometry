import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_appFullRS_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g r a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r c x
          ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨C, hC_nn, fun W x => ?_⟩
  rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W x]
  exact hC x (W.toSection x)

abbrev HomTensorRSField (r a c : ℕ) (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] : Type _ :=
  Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSFieldApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) : SmoothCcTensor g r
      c :=
  homTensorRSApply (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
@[simp] lemma appFullSec_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSFieldApply (I := I) (M := M) g r a c Q W).toSection x =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x) (W.toSection x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullSec_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa + Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W + homTensorRSFieldApply (I := I) (M := M)
        g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W +
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x +
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa + Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) +
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_add, Pi.add_apply]]
  rw [ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullSec_zero_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (0 : HomTensorRSField (E := E) (M := M) r a c I)
      W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  rw [show ((0 : HomTensorRSField (E := E) (M := M) r a c I) x :
      TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) = 0 from by
    rw [ContMDiffSection.coe_zero, Pi.zero_apply]]
  rw [ContinuousLinearMap.zero_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullSec_sub_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa - Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W - homTensorRSFieldApply (I := I) (M := M)
        g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W -
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x -
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa - Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) -
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [ContinuousLinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) : HomTensorRSField (E := E) (M := M) r a
      (c + 1) I where
  toFun := fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x
  contMDiff_toFun :=
    homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma homTensorRSCovGradSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        homTensorRSCovGradSec (I := I) (M := M) g r a c Q x) =
      homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x := rfl

set_option backward.isDefEq.respectTransparency false in

noncomputable def slotExtendFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r (a + 1) (c + 1) I where
  toFun := fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Q x)
  contMDiff_toFun :=
    slotExtendFullFib_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma slotExtendFullSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        slotExtendFullSec (I := I) (M := M) g r a c Q x) =
      slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Q x) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_appFullSec_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (homTensorRSFieldApply (I := I) (M := M) g r a c Q W) =
      homTensorRSFieldApply (I := I) (M := M) g r a (c + 1)
        (homTensorRSCovGradSec (I := I) (M := M) g r a c Q) W +
        homTensorRSFieldApply (I := I) (M := M) g r (a + 1) (c + 1)
          (slotExtendFullSec (I := I) (M := M) g r a c Q)
          (covGrad (I := I) (M := M) g r a W) :=
  covGrad_appFullRS_eq (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W


def castHomTensorRSFieldTgt {c c' : ℕ} (r a : ℕ) (h : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a c' I :=
  h ▸ Q


def castHomTensorRSFieldSrc {a a' : ℕ} (r c : ℕ) (h : a = a')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a' c I :=
  h ▸ Q

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullSec_castRankCc_db {a a' c c' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hc : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (V : SmoothCcTensor g r a) :
    castCcTensorRank g r hc (homTensorRSFieldApply (I := I) (M := M) g r a c Q V) =
      homTensorRSFieldApply (I := I) (M := M) g r a' c'
        (castHomTensorRSFieldSrc (E := E) (M := M) r c' ha
        (castHomTensorRSFieldTgt (E := E) (M := M) r a hc Q)) (castCcTensorRank g r ha V) := by
  subst ha; subst hc; rfl
end Connection
end Geometry
end DifferentialGeometry

end
