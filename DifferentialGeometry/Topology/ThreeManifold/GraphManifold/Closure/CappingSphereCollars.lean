import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.CoreBoundaryCollar

/-!
Full normalized signed sphere collars with their actual positive-side capped-core formula.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private def sphereNormalScale (δ : ℝ) (hδ : 0 < δ) : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ where
  toFun s := δ * s
  invFun s := s / δ
  left_inv s := by simp [hδ.ne']
  right_inv s := by field_simp [hδ.ne']
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => δ * s)
    apply ContDiff.contMDiff
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => s / δ)
    apply ContDiff.contMDiff
    fun_prop

theorem exists_cappingSphereSignedCollar
    {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (C : SphericalCapping M N T) (b : T.Boundary) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
      (d : PartialDiffeomorph sphereSignedCollarModel (𝓡 3)
        (ClosureSphere.{u} × ℝ) N.Carrier ∞),
      d.source = sphereSignedCollarSource ∧
      (∀ z, d (z, 0) = C.cap b (sphereToClosedCell z.down)) ∧
      ∀ z (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1), d (z, s) =
        C.coreInclusionHalfCollar b (z.down,
          ⟨δ * s, mul_nonneg hδ.le hs, by nlinarith⟩) := by
  obtain ⟨a, hwidth, ha⟩ := C.exists_coreBoundaryCollar b
  let l := a.reparametrize (uliftDiffeomorph (𝓡 2) SphereTwo).symm
  let e := (Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).prodCongr
    (sphereNormalScale a.radius a.radius_pos)
  let d := e.toPartialDiffeomorph.trans l.toPartialDiffeomorph
  have hsource : d.source = sphereSignedCollarSource := by
    change univ ∩ (fun p : ClosureSphere.{u} × ℝ => (p.1, a.radius * p.2)) ⁻¹'
      l.toPartialDiffeomorph.source = _
    rw [l.toPartialDiffeomorph_source]
    ext p
    change (True ∧ (True ∧ -a.radius < a.radius * p.2 ∧ a.radius * p.2 < a.radius)) ↔
      True ∧ -1 < p.2 ∧ p.2 < 1
    simp only [true_and]
    constructor
    · intro hp
      constructor <;> nlinarith [a.radius_pos]
    · intro hp
      constructor <;> nlinarith [a.radius_pos]
  refine ⟨a.radius, a.radius_pos, hwidth, d, hsource, ?_, ?_⟩
  · intro z
    change l.toPartialDiffeomorph (z, a.radius * 0) = _
    rw [mul_zero]
    exact l.toPartialDiffeomorph_apply
      (z, ⟨0, neg_lt_zero.mpr a.radius_pos, a.radius_pos⟩) |>.trans (l.toFun_zero z)
  · intro z s hs hs1
    have hleft : -a.radius < a.radius * s := by nlinarith [a.radius_pos]
    have hright : a.radius * s < a.radius := by nlinarith [a.radius_pos]
    change l.toPartialDiffeomorph (z, a.radius * s) = _
    rw [l.toPartialDiffeomorph_apply (z, ⟨a.radius * s, hleft, hright⟩)]
    exact ha (z.down, ⟨a.radius * s, hleft, hright⟩) (mul_nonneg a.radius_pos.le hs)

end GC.GraphManifold
