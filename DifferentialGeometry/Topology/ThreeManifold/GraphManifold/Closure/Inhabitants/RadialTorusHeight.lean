import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCarrier

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

theorem radial_height_regular (p : SphereCarrier.{0})
    (hp : -1 < cliffordHeight p ∧ cliffordHeight p < 1) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cliffordHeight p ≠ 0 := by
  have hfirst : sphereFirst p ≠ 0 := by
    intro hzero
    have hnorm := norm_sphereFirst_sq_eq p
    rw [hzero, norm_zero, zero_pow (by decide)] at hnorm
    linarith [hp.1]
  have hsecond : sphereSecond p ≠ 0 := by
    intro hzero
    have hnorm := norm_sphereSecond_sq_eq p
    rw [hzero, norm_zero, zero_pow (by decide)] at hnorm
    linarith [hp.2]
  let q := cliffordSeamInv.{0} p
  have hq : q ∈ cliffordSeam.{0}.source := cliffordSeam.{0}.map_target' ⟨hfirst, hsecond⟩
  have he : cliffordSeam.{0} q = p := cliffordSeam.{0}.right_inv' ⟨hfirst, hsecond⟩
  have hcoord : cliffordHeight ∘ cliffordSeam.{0} =ᶠ[𝓝 q] Prod.snd := by
    filter_upwards [cliffordSeam.{0}.open_source.mem_nhds hq] with z hz
    change cliffordHeight (cliffordSeamMap z) = z.2
    rw [cliffordHeight_cliffordSeamMap, seamClamp_of_mem hz.1.le hz.2.le]
  intro hzero
  have hchain := mfderiv_comp q
    (contMDiff_cliffordHeight.mdifferentiableAt (by simp))
    (cliffordSeam.{0}.mdifferentiableAt (by simp) hq)
  erw [hcoord.mfderiv_eq, mfderiv_snd, he, hzero, ContinuousLinearMap.zero_comp] at hchain
  have hvalue := DFunLike.congr_fun hchain ((0 : TangentSpace torusModel q.1), (1 : ℝ))
  change (1 : ℝ) = 0 at hvalue
  exact one_ne_zero hvalue

def bandDefiner (a b : ℝ) (p : SphereCarrier.{0}) : ℝ :=
  (cliffordHeight p - a) * (cliffordHeight p - b)

theorem bandDefiner_smooth (a b : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (bandDefiner a b) :=
  (contMDiff_cliffordHeight.sub contMDiff_const).mul
    (contMDiff_cliffordHeight.sub contMDiff_const)

theorem radial_mvfderiv_regular (p : SphereCarrier.{0})
    (hp : -1 < cliffordHeight p ∧ cliffordHeight p < 1) :
    mvfderiv (𝓡 3) cliffordHeight p ≠ 0 := by
  intro hzero
  apply radial_height_regular p hp
  ext v
  apply (NormedSpace.fromTangentSpace (cliffordHeight p)).injective
  have h := DFunLike.congr_fun hzero v
  simpa only [mvfderiv, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearEquiv.coe_coe, map_zero] using h

theorem bandDefiner_regular (a b : ℝ) (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (p : SphereCarrier.{0}) (hp : bandDefiner a b p = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (bandDefiner a b) p ≠ 0 := by
  have hd := contMDiff_cliffordHeight.mdifferentiableAt (x := p) (by simp)
  have hda : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun x : SphereCarrier.{0} => cliffordHeight x - a) p :=
    (contMDiff_cliffordHeight.sub contMDiff_const).mdifferentiableAt (by simp)
  have hdb : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun x : SphereCarrier.{0} => cliffordHeight x - b) p :=
    (contMDiff_cliffordHeight.sub contMDiff_const).mdifferentiableAt (by simp)
  intro hzero
  have hz : mvfderiv (𝓡 3) (bandDefiner a b) p = 0 := by
    simp only [mvfderiv, hzero, ContinuousLinearMap.comp_zero]
  change (cliffordHeight p - a) * (cliffordHeight p - b) = 0 at hp
  change mvfderiv (𝓡 3)
    (fun x => (cliffordHeight x - a) * (cliffordHeight x - b)) p = 0 at hz
  rw [mvfderiv_fun_mul hda hdb] at hz
  rw [mvfderiv_fun_sub (g := cliffordHeight) (g' := fun _ => a) hd mdifferentiableAt_const,
    mvfderiv_fun_sub (g := cliffordHeight) (g' := fun _ => b) hd mdifferentiableAt_const] at hz
  simp only [mvfderiv_const, sub_zero] at hz
  rcases mul_eq_zero.mp hp with hp | hp
  · have he : cliffordHeight p = a := sub_eq_zero.mp hp
    have hreg := radial_mvfderiv_regular p ⟨by linarith, by linarith⟩
    simp only [he, sub_self, zero_smul, zero_add] at hz
    exact smul_ne_zero (sub_ne_zero.mpr hab.ne) hreg hz
  · have he : cliffordHeight p = b := sub_eq_zero.mp hp
    have hreg := radial_mvfderiv_regular p ⟨by linarith, by linarith⟩
    simp only [he, sub_self, zero_smul, add_zero] at hz
    exact smul_ne_zero (sub_ne_zero.mpr hab.ne') hreg hz

theorem bandDefiner_nonpos_iff {a b : ℝ} (hab : a ≤ b) {p : SphereCarrier.{0}} :
    bandDefiner a b p ≤ 0 ↔ a ≤ cliffordHeight p ∧ cliffordHeight p ≤ b := by
  unfold bandDefiner
  rw [mul_nonpos_iff]
  constructor
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · constructor <;> linarith
    · constructor <;> linarith
  · intro hp
    exact Or.inl ⟨sub_nonneg.mpr hp.1, sub_nonpos.mpr hp.2⟩

theorem bandDefiner_zero_iff {a b : ℝ} {p : SphereCarrier.{0}} :
    bandDefiner a b p = 0 ↔ cliffordHeight p = a ∨ cliffordHeight p = b := by
  simp only [bandDefiner, mul_eq_zero, sub_eq_zero]

end GC.GraphManifold.Assembly.FC39P0.X135Radial
