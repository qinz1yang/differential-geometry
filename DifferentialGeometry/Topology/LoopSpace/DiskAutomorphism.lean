import DifferentialGeometry.Topology.LoopSpace.SpanningDisk.Reparametrization
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Argument
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Transitivity

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Topology

def diskAutomorphismBoundary (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    loopCircle ≃ₜ loopCircle :=
  ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
    (Complex.diskAutomorphismCircle a η ha hη)).trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

theorem diskAutomorphismBoundary_toCircle (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (θ : loopCircle) :
    AddCircle.toCircle (diskAutomorphismBoundary a η ha hη θ) =
      Complex.diskAutomorphismCircle a η ha hη (AddCircle.toCircle θ) := by
  have h := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply
    (Complex.diskAutomorphismCircle a η ha hη (AddCircle.toCircle θ))
  simpa only [diskAutomorphismBoundary, Homeomorph.trans_apply,
    AddCircle.homeomorphCircle_apply] using h

theorem diskAutomorphism_diskBoundary (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (θ : loopCircle) :
    Complex.diskAutomorphism a η ha hη (diskBoundary θ) =
      diskBoundary (diskAutomorphismBoundary a η ha hη θ) := by
  apply Subtype.ext
  change η * Complex.diskMoebius a (AddCircle.toCircle θ) =
    (AddCircle.toCircle (diskAutomorphismBoundary a η ha hη θ) : ℂ)
  rw [diskAutomorphismBoundary_toCircle, Complex.coe_diskAutomorphismCircle_apply]


private theorem strictMono_of_continuous_circle_lift
    (δ : loopCircle ≃ₜ loopCircle) (f : ℝ → ℝ) (hf : Continuous f)
    (hp : ∀ t, f (t + 1) = f t + 1)
    (hlift : ∀ t : ℝ, (f t : loopCircle) = δ (t : loopCircle)) : StrictMono f := by
  have hper : Function.Periodic (fun t => f t - t) 1 := by
    intro t
    dsimp only
    rw [hp]
    ring
  have hinj : Function.Injective f := by
    intro x y hxy
    have he : (x : loopCircle) = (y : loopCircle) := by
      apply δ.injective
      rw [← hlift x, ← hlift y, hxy]
    have hz : ((x - y : ℝ) : loopCircle) = 0 := by rw [AddCircle.coe_sub, he, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
    have hn' : x = y + (n : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hn
      linarith
    have hi := hper.int_mul n y
    simp only [mul_one] at hi
    rw [← hn', hxy] at hi
    linarith
  rcases hf.strictMono_of_inj hinj with hmono | hanti
  · exact hmono
  · have h := hanti (show (0 : ℝ) < 1 by norm_num)
    have h1 := hp 0
    simp only [zero_add] at h1
    linarith

theorem diskBoundaryArgumentLift_coe (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) (t : ℝ) :
    (Complex.diskBoundaryArgumentLift a η t : loopCircle) =
      diskAutomorphismBoundary a η ha hη (t : loopCircle) := by
  apply (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective
  simp only [AddCircle.homeomorphCircle_apply]
  rw [diskAutomorphismBoundary_toCircle]
  apply Subtype.ext
  rw [Complex.coe_diskAutomorphismCircle_apply, AddCircle.toCircle_apply_mk,
    AddCircle.toCircle_apply_mk]
  simp only [Circle.coe_exp, div_one]
  exact Complex.exp_diskBoundaryArgumentLift ha hη t


theorem exists_smooth_circleDeg1Lift_diskAutomorphismBoundary
    (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    ∃ h : CircleDeg1Lift, ContDiff ℝ ∞ h ∧ StrictMono h ∧
      ∀ t : ℝ, (h t : loopCircle) = diskAutomorphismBoundary a η ha hη (t : loopCircle) := by
  have hs := Complex.contDiff_diskBoundaryArgumentLift ha η
  have hm := strictMono_of_continuous_circle_lift (diskAutomorphismBoundary a η ha hη)
    (Complex.diskBoundaryArgumentLift a η) hs.continuous
    (Complex.diskBoundaryArgumentLift_add_one a η) (diskBoundaryArgumentLift_coe a η ha hη)
  let h : CircleDeg1Lift :=
    { toFun := Complex.diskBoundaryArgumentLift a η
      monotone' := hm.monotone
      map_add_one' := Complex.diskBoundaryArgumentLift_add_one a η }
  exact ⟨h, hs, hm, diskBoundaryArgumentLift_coe a η ha hη⟩

theorem exists_continuous_circleDeg1Lift_diskAutomorphismBoundary
    (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    ∃ h : CircleDeg1Lift, Continuous h ∧ StrictMono h ∧
      ∀ t : ℝ, (h t : loopCircle) = diskAutomorphismBoundary a η ha hη (t : loopCircle) := by
  obtain ⟨h, hs, hm, he⟩ := exists_smooth_circleDeg1Lift_diskAutomorphismBoundary a η ha hη
  exact ⟨h, hs.continuous, hm, he⟩

end DifferentialGeometry.Topology

end

noncomputable section

open Set
open scoped ComplexConjugate



namespace DifferentialGeometry.Topology

theorem exists_diskAutomorphismBoundary_map_cyclic_triples
    (s₀ s₁ s₂ t₀ t₁ t₂ : ℝ)
    (hs₁ : s₀ < s₁) (hs₂ : s₁ < s₂) (hs₃ : s₂ < s₀ + 1)
    (ht₁ : t₀ < t₁) (ht₂ : t₁ < t₂) (ht₃ : t₂ < t₀ + 1) :
    ∃ a η : ℂ, ∃ ha : ‖a‖ < 1, ∃ hη : ‖η‖ = 1,
      diskAutomorphismBoundary a η ha hη (s₀ : loopCircle) = (t₀ : loopCircle) ∧
      diskAutomorphismBoundary a η ha hη (s₁ : loopCircle) = (t₁ : loopCircle) ∧
      diskAutomorphismBoundary a η ha hη (s₂ : loopCircle) = (t₂ : loopCircle) := by
  obtain ⟨a, η, ha, hη, h0, h1, h2⟩ :=
    Complex.exists_diskMoebius_map_cyclic_triples s₀ s₁ s₂ t₀ t₁ t₂ hs₁ hs₂ hs₃ ht₁ ht₂ ht₃
  have hconv {s t : ℝ}
      (h : η * Complex.diskMoebius a (Complex.exp ((2 * Real.pi * s : ℝ) * Complex.I)) =
        Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) :
      diskAutomorphismBoundary a η ha hη (s : loopCircle) = (t : loopCircle) := by
    apply (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective
    simp only [AddCircle.homeomorphCircle_apply]
    rw [diskAutomorphismBoundary_toCircle]
    apply Subtype.ext
    rw [Complex.coe_diskAutomorphismCircle_apply, AddCircle.toCircle_apply_mk,
      AddCircle.toCircle_apply_mk]
    simpa only [Circle.coe_exp, div_one] using h
  exact ⟨a, η, ha, hη, hconv h0, hconv h1, hconv h2⟩

theorem exists_diskAutomorphismBoundary_three_point_normalization
    (σ : C(loopCircle, loopCircle)) (f : CircleDeg1Lift) (hf : Continuous f)
    (hσ : ∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle))
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ a η : ℂ, ∃ ha : ‖a‖ < 1, ∃ hη : ‖η‖ = 1,
      σ (diskAutomorphismBoundary a η ha hη 0) = 0 ∧
      σ (diskAutomorphismBoundary a η ha hη (p : loopCircle)) = (p : loopCircle) ∧
      σ (diskAutomorphismBoundary a η ha hη (q : loopCircle)) = (q : loopCircle) := by
  have hsur := (CircleDeg1Lift.continuous_iff_surjective f).mp hf
  obtain ⟨s₀, hs₀⟩ := hsur 0
  obtain ⟨s₁, hs₁⟩ := hsur p
  obtain ⟨s₂, hs₂⟩ := hsur q
  have h01 : s₀ < s₁ := by
    by_contra h
    have hh := f.monotone (le_of_not_gt h)
    rw [hs₀, hs₁] at hh
    linarith
  have h12 : s₁ < s₂ := by
    by_contra h
    have hh := f.monotone (le_of_not_gt h)
    rw [hs₁, hs₂] at hh
    linarith
  have h20 : s₂ < s₀ + 1 := by
    by_contra h
    have hh := f.monotone (le_of_not_gt h)
    rw [f.map_add_one, hs₀, hs₂] at hh
    linarith
  obtain ⟨a, η, ha, hη, h0, h1, h2⟩ :=
    exists_diskAutomorphismBoundary_map_cyclic_triples 0 p q s₀ s₁ s₂ hp hpq
      (by simpa using hq) h01 h12 h20
  refine ⟨a, η, ha, hη, ?_, ?_, ?_⟩
  · simpa only [AddCircle.coe_zero, h0, ← hσ, hs₀] using congrArg σ h0
  · rw [h1, ← hσ, hs₁]
  · rw [h2, ← hσ, hs₂]

end DifferentialGeometry.Topology

end
