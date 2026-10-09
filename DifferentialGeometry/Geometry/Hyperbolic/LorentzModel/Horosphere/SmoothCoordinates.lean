import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Coordinates
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

private theorem contMDiff_upper_time (n : ℕ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r
      (fun x : Hyperbolic.HUpper n => Hyperbolic.tc x.val) :=
  Hyperboloid.contMDiff_time.comp (Hyperboloid.hUpperDiffeomorph n r).contMDiff

private theorem contMDiff_upper_coordinate (n : ℕ) (r : ℕ∞ω) (i : Fin n) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r
      (fun x : Hyperbolic.HUpper n => x.val (Sum.inl i)) := by
  have hc : ContDiff ℝ r (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
    (contDiff_apply ℝ ℝ i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff
  exact hc.contMDiff.comp
    (Hyperboloid.contMDiff_space.comp (Hyperboloid.hUpperDiffeomorph n r).contMDiff)

namespace Busemann

open Hyperbolic HyperbolicBoundary

theorem busemann_eq_log_native {n : ℕ} (ξ : BoundaryH n) (x : HUpper n) :
    busemann ξ x = Real.log ((Hyperboloid.hUpperIsometryEquiv n x).time -
      inner ℝ (Hyperboloid.hUpperIsometryEquiv n x).space (BoundaryTopology.spatial ξ)) := by
  have hi : inner ℝ (Hyperboloid.hUpperIsometryEquiv n x).space (BoundaryTopology.spatial ξ) =
      sdot x.val ξ.val := by
    simp only [PiLp.inner_apply, Real.inner_apply, Hyperboloid.hUpperIsometryEquiv_space_apply,
      BoundaryTopology.spatial_apply, sdot]
  rw [hi, Hyperboloid.hUpperIsometryEquiv_time]
  change Real.log (-(sdot x.val ξ.val - tc x.val * tc ξ.val)) = _
  rw [ξ.tc_eq, mul_one, neg_sub]
  rfl

theorem contMDiff_busemann {n : ℕ} (ξ : BoundaryH n) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r (busemann ξ) := by
  have hsum : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r
      (fun x : HUpper n => sdot x.val ξ.val) := by
    unfold sdot
    exact ContMDiff.sum fun i _ => (contMDiff_upper_coordinate n r i).mul contMDiff_const
  have harg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r
      (fun x : HUpper n => -lorB x.val ξ.val) := by
    have h := ((contMDiff_upper_time n r).mul (contMDiff_const (c := tc ξ.val))).sub hsum
    simpa only [lorB, neg_sub, Pi.mul_apply] using h
  intro x
  exact (Real.contDiffAt_log.mpr (neg_lorB_upper_boundary_pos x ξ).ne').contMDiffAt.comp x (harg x)

end Busemann

namespace Horospherical

open Hyperbolic

local notation "P" => (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi)

private theorem contMDiff_height (m : ℕ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, ℝ) r
      (height : HUpper (m + 1) → ℝ) := by
  exact ((contMDiff_upper_time (m + 1) r).sub
    (contMDiff_upper_coordinate (m + 1) r (Fin.last m))).inv₀
      (fun x => (vHeight_pos x).ne')

private theorem contMDiff_horizontal (m : ℕ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, Horizontal m) r
      (horizontal : HUpper (m + 1) → Horizontal m) := by
  have hraw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, Fin m → ℝ) r
      (fun x : HUpper (m + 1) => fun i : Fin m => x.val (Sum.inl i.castSucc)) :=
    contMDiff_pi_space.mpr fun i => contMDiff_upper_coordinate (m + 1) r i.castSucc
  have hs := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.contDiff.contMDiff.comp hraw
  exact (contMDiff_height m r).smul hs

private theorem contMDiff_coordsEquiv (m : ℕ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      ((𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ)) r
      (fun x : HUpper (m + 1) => (horizontal x, (⟨height x, height_pos x⟩ : P))) := by
  have hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, ℝ) r
      (fun x : HUpper (m + 1) => (⟨height x, height_pos x⟩ : P)) := by
    apply (Manifold.contMDiff_subtypeVal_comp_iff (n := r) P _).mp
    exact contMDiff_height m r
  exact (contMDiff_horizontal m r).prodMk hh

private theorem contMDiff_ofCoords (m : ℕ) (r : ℕ∞ω) :
    ContMDiff ((𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) r
      (fun p : Horizontal m × P => ofCoords p.1 p.2.val p.2.property) := by
  let I := (𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ)
  have hh : ContMDiff I 𝓘(ℝ, ℝ) r (fun p : Horizontal m × P => p.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hinv := hh.inv₀ (fun p => p.2.property.ne')
  have hnorm : ContMDiff I 𝓘(ℝ, ℝ) r (fun p : Horizontal m × P => ‖p.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).contMDiff.comp contMDiff_fst
  have hc (i : Fin m) : ContMDiff I 𝓘(ℝ, ℝ) r
      (fun p : Horizontal m × P => p.1 i) :=
    ((contDiff_apply ℝ ℝ i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).contDiff).contMDiff.comp contMDiff_fst
  have hraw : ContMDiff I 𝓘(ℝ, Fin (m + 1) → ℝ) r
      (fun p : Horizontal m × P => fun j =>
        (ofCoords p.1 p.2.val p.2.property).val (Sum.inl j)) := by
    apply contMDiff_pi_space.mpr
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [ofCoords, ofCoordsVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        MobiusBoundary.horoVec_last, MobiusBoundary.ptInfty_val_last, mul_one]
      simp_rw [normSq_horizontal]
      exact (hinv.mul ((hnorm.sub contMDiff_const).div_const 2)).add (hh.div_const 2)
    · simp only [ofCoords, ofCoordsVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        MobiusBoundary.horoVec_castSucc, MobiusBoundary.ptInfty_val_castSucc, mul_zero, add_zero]
      exact hinv.mul (hc i)
  have hs := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm.contDiff.contMDiff.comp hraw
  have hnative := Hyperboloid.contMDiff_ofSpace.comp hs
  have hupper := (Hyperboloid.hUpperDiffeomorph (m + 1) r).symm.contMDiff.comp hnative
  apply hupper.congr
  intro p
  dsimp only [Function.comp_def]
  apply (Hyperboloid.hUpperIsometryEquiv (m + 1)).injective
  rw [Hyperboloid.hUpperDiffeomorph_symm_apply, IsometryEquiv.apply_symm_apply]
  apply Hyperboloid.ext
  apply PiLp.ext
  intro j
  exact Hyperboloid.hUpperIsometryEquiv_space_apply (m + 1) _ j

def coordsDiffeomorph (m : ℕ) (r : ℕ∞ω := ∞) :
    HUpper (m + 1) ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))),
      ((𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ))⟯ Horizontal m × P where
  toEquiv := coordsEquiv
  contMDiff_toFun := contMDiff_coordsEquiv m r
  contMDiff_invFun := contMDiff_ofCoords m r

@[simp] theorem coordsDiffeomorph_toEquiv (m : ℕ) (r : ℕ∞ω) :
    (coordsDiffeomorph m r).toEquiv = coordsEquiv := rfl

@[simp] theorem coordsDiffeomorph_apply (m : ℕ) (r : ℕ∞ω) (x : HUpper (m + 1)) :
    coordsDiffeomorph m r x = (horizontal x, ⟨height x, height_pos x⟩) := rfl

@[simp] theorem coordsDiffeomorph_symm_apply (m : ℕ) (r : ℕ∞ω) (p : Horizontal m × P) :
    (coordsDiffeomorph m r).symm p = ofCoords p.1 p.2.val p.2.property := rfl

end Horospherical
end DifferentialGeometry
