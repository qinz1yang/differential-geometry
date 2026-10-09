import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceFrameC12X
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion

/-!
# Splice: the recentring map and frame identities (C12X, O-C12X-S16H G4e2)

The target neck embedding of the far-early branch is `Ψ ∘ A`, where `Ψ : W → M` is the survivor
pull-in of a tube (`W` open in the neck buffer) and `A z = (z.1, u + λ z.2)` recentres at the
point and stretches axially.  This file provides

* `s16hAffine_C12X u λ` (a diffeomorphism of the cylinder) and its derivative;
* `affineInto_C12X`: its restriction from the target buffer into the tube, a local
  diffeomorphism with derivative `(a.1, λ a.2)`;
* `localPull_affine_cylFam_C12X`: `A^*(κ · cylFam v) = cyl2 (1 - κ (1 - v)) (κ λ²)` (exact).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance s16h_sphereDim5 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

/-- The axial recentring/stretch `(ω, z) ↦ (ω, u + λ z)` of the cylinder. -/
def s16hAffine_C12X (u lam : ℝ) (hlam : lam ≠ 0) :
    SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
      SpatialNeckCylinder where
  toEquiv :=
    { toFun := fun x => (x.1, u + lam * x.2)
      invFun := fun x => (x.1, lam⁻¹ * (x.2 - u))
      left_inv := by
        intro x
        apply Prod.ext
        · rfl
        · change lam⁻¹ * (u + lam * x.2 - u) = x.2
          rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · change u + lam * (lam⁻¹ * (x.2 - u)) = x.2
          rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul, add_sub_cancel] }
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul contMDiff_snd))
  contMDiff_invFun :=
    contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_snd.sub contMDiff_const))

@[simp] theorem s16hAffine_C12X_apply (u lam : ℝ) (hlam : lam ≠ 0) (x : SpatialNeckCylinder) :
    s16hAffine_C12X u lam hlam x = (x.1, u + lam * x.2) := rfl

/-- Derivative of the affine map. -/
theorem s16hAffine_C12X_mfderiv (u lam : ℝ) (hlam : lam ≠ 0) (x : SpatialNeckCylinder)
    (V : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel (s16hAffine_C12X u lam hlam) x V =
      (V.1, lam * V.2) := by
  have hd : HasFDerivAt (fun z : ℝ => u + lam * z) (lam • ContinuousLinearMap.id ℝ ℝ) x.2 :=
    ((hasFDerivAt_id x.2).const_smul lam).const_add u
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => u + lam * z) x.2 :=
    hd.differentiableAt.mdifferentiableAt
  have hfun : (s16hAffine_C12X u lam hlam : SpatialNeckCylinder → SpatialNeckCylinder) =
      Prod.map (id : SpatialNeckSphere → SpatialNeckSphere) (fun z : ℝ => u + lam * z) := rfl
  rw [hfun, mfderiv_prodMap mdifferentiableAt_id hm, mfderiv_id]
  change (V.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => u + lam * z) x.2 V.2) = _
  rw [mfderiv_eq_fderiv, hd.fderiv]
  rfl

/-- The affine map from the target buffer into a tube `W` of a neck buffer. -/
def affineInto_C12X (ε δ u lam : ℝ) (hlam : lam ≠ 0) (W : TopologicalSpace.Opens (neckBuffer δ))
    (hW : ∀ z : spatialNeckBuffer ε, ∃ h : s16hAffine_C12X u lam hlam z.val ∈ neckBuffer δ,
      (⟨s16hAffine_C12X u lam hlam z.val, h⟩ : neckBuffer δ) ∈ W) :
    spatialNeckBuffer ε → W :=
  fun z => ⟨⟨s16hAffine_C12X u lam hlam z.val, (hW z).1⟩, (hW z).2⟩

section AffineInto

variable {ε δ u lam : ℝ} {hlam : lam ≠ 0} {W : TopologicalSpace.Opens (neckBuffer δ)}
  {hW : ∀ z : spatialNeckBuffer ε, ∃ h : s16hAffine_C12X u lam hlam z.val ∈ neckBuffer δ,
    (⟨s16hAffine_C12X u lam hlam z.val, h⟩ : neckBuffer δ) ∈ W}

theorem affineInto_C12X_val_val (z : spatialNeckBuffer ε) :
    ((affineInto_C12X ε δ u lam hlam W hW z : neckBuffer δ) : NeckCylinder) =
      s16hAffine_C12X u lam hlam z.val := rfl

/-- The affine map into the tube is a local diffeomorphism. -/
theorem affineInto_C12X_isLocalDiffeomorph :
    IsLocalDiffeomorph SpatialNeckCylinderModel NeckCylinderModel ∞
      (affineInto_C12X ε δ u lam hlam W hW) := by
  intro z
  have h0 : IsLocalDiffeomorph SpatialNeckCylinderModel SpatialNeckCylinderModel ∞
      (fun x : spatialNeckBuffer ε => s16hAffine_C12X u lam hlam x) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open (spatialNeckBuffer ε)
      ((s16hAffine_C12X u lam hlam).isLocalDiffeomorph.isLocalDiffeomorphOn _)
  have h1 : IsLocalDiffeomorphAt SpatialNeckCylinderModel NeckCylinderModel ∞
      (fun x : spatialNeckBuffer ε =>
        (⟨s16hAffine_C12X u lam hlam x.val, (hW x).1⟩ : neckBuffer δ)) z :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun x => (hW x).1) (h0 z)
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun x => (hW x).2) h1

/-- Derivative of the affine map into the tube. -/
theorem affineInto_C12X_mfderiv (z : spatialNeckBuffer ε)
    (a : TangentSpace SpatialNeckCylinderModel z) :
    mfderiv SpatialNeckCylinderModel NeckCylinderModel (affineInto_C12X ε δ u lam hlam W hW) z a =
      (a.1, lam * a.2) := by
  let F := affineInto_C12X ε δ u lam hlam W hW
  have hF : MDifferentiableAt SpatialNeckCylinderModel NeckCylinderModel F z :=
    (affineInto_C12X_isLocalDiffeomorph z).mdifferentiableAt (by decide)
  have hv1 : MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Subtype.val : W → neckBuffer δ) (F z) :=
    (contMDiff_subtype_val (I := NeckCylinderModel) (U := W) (n := ∞)).mdifferentiableAt
      (by decide)
  have hv2 : MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Subtype.val : neckBuffer δ → NeckCylinder) (F z).val :=
    (contMDiff_subtype_val (I := NeckCylinderModel) (U := neckBuffer δ) (n := ∞)).mdifferentiableAt
      (by decide)
  have hv0 : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : spatialNeckBuffer ε → SpatialNeckCylinder) z :=
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (U := spatialNeckBuffer ε)
      (n := ∞)).mdifferentiableAt (by decide)
  have hE : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (s16hAffine_C12X u lam hlam) z.val :=
    (s16hAffine_C12X u lam hlam).mdifferentiable (by decide) z.val
  have hcomp : (fun x => ((F x : neckBuffer δ) : NeckCylinder)) =
      (s16hAffine_C12X u lam hlam) ∘ (Subtype.val : spatialNeckBuffer ε → SpatialNeckCylinder) :=
    rfl
  have h1 : mfderiv SpatialNeckCylinderModel NeckCylinderModel
      (fun x => ((F x : neckBuffer δ))) z a =
      mfderiv SpatialNeckCylinderModel NeckCylinderModel F z a := by
    have h := mfderiv_comp_apply (I := SpatialNeckCylinderModel) (I' := NeckCylinderModel)
      (I'' := NeckCylinderModel) z hv1 hF a
    rw [mfderiv_subtype_val_apply] at h
    exact h
  have h2 : mfderiv SpatialNeckCylinderModel NeckCylinderModel
      (fun x => ((F x : neckBuffer δ) : NeckCylinder)) z a =
      mfderiv SpatialNeckCylinderModel NeckCylinderModel (fun x => ((F x : neckBuffer δ))) z a := by
    have h := mfderiv_comp_apply (I := SpatialNeckCylinderModel) (I' := NeckCylinderModel)
      (I'' := NeckCylinderModel) z hv2 (hv1.comp z hF) a
    rw [mfderiv_subtype_val_apply] at h
    exact h
  have hL := h2.trans h1
  have hR : mfderiv SpatialNeckCylinderModel NeckCylinderModel
      (fun x => ((F x : neckBuffer δ) : NeckCylinder)) z a = (a.1, lam * a.2) := by
    rw [hcomp]
    have h3 := mfderiv_comp_apply (I := SpatialNeckCylinderModel)
      (I' := SpatialNeckCylinderModel) (I'' := SpatialNeckCylinderModel) z hE hv0 a
    rw [mfderiv_subtype_val_apply] at h3
    exact h3.trans (s16hAffine_C12X_mfderiv u lam hlam z.val a)
  rw [← hL, hR]

/-- **Exact frame identity for the cylinder.**
`A^*(κ · cylFam v) = cyl2 (1 - κ (1 - v)) (κ λ²)`. -/
theorem localPull_affine_cylFam_C12X {κ v : ℝ} (hκ : 0 < κ) (hv : v < 1)
    (hσ : 1 - κ * (1 - v) < 1) (hc : 0 < κ * lam ^ 2) :
    localPullMetric (scaleMetric κ hκ
        (((cylFam_C12X v).restrictOpen (neckBuffer δ)).restrictOpen W))
        (affineInto_C12X ε δ u lam hlam W hW) affineInto_C12X_isLocalDiffeomorph =
      (cyl2_C12X (1 - κ * (1 - v)) (κ * lam ^ 2)).restrictOpen (spatialNeckBuffer ε) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z a b
  have hda := affineInto_C12X_mfderiv (hW := hW) z a
  have hdb := affineInto_C12X_mfderiv (hW := hW) z b
  rw [localPullMetric_inner, scaleMetric_inner, hda, hdb]
  change κ * (cylFam_C12X v).inner (s16hAffine_C12X u lam hlam z.val) (a.1, lam * a.2)
      (b.1, lam * b.2) = (cyl2_C12X (1 - κ * (1 - v)) (κ * lam ^ 2)).inner z.val a b
  have e1 := cylFam_inner_C12X hv (s16hAffine_C12X u lam hlam z.val)
    ((a.1, lam * a.2) : TangentSpace SpatialNeckCylinderModel (s16hAffine_C12X u lam hlam z.val))
    (b.1, lam * b.2)
  have e2 := cyl2_inner_C12X hσ hc z.val a b
  simp only [s16hAffine_C12X_apply] at e1 ⊢
  linear_combination κ * e1 - e2

end AffineInto

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
