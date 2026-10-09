import DifferentialGeometry.Topology.Ehresmann.ArcEndSideG6C
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The side function of an arc end through a product chart (lane O-G6C, G2l)

`slimEnd_side_of_chart_G6C`: for a map `f : M → H` with a smooth product chart `φ : ℝ¹ × F → M`
over a smooth immersed curve `σ` of the base (`f ∘ φ = σ ∘ fst`, `range φ = X ∩ f⁻¹(range σ)`),
an arc `γ` of the base starting at `a = σ 0` and a set `K` equal to the arc near `a`, the affine
function `χ = c · ℓ(· − a)` of `exists_side_function_G6C` satisfies, besides `K = {χ ≥ 0}` and
`χ = 0 ↔ · = a` on the base near `a`:
* every point `p ∈ X` over `a` is a limit of points `q ∈ X` with `f q` near `a` and `χ (f q) < 0`;
* `d(χ ∘ f)_p ≠ 0` at every point `p ∈ X` over `a` where `f` is differentiable.
-/

set_option autoImplicit false

open Set Function Topology Filter Manifold
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- **The side function of an arc end through a product chart.** -/
theorem slimEnd_side_of_chart_G6C {f : M → H} {X : Set M} {B O K N₀ : Set H} {a : H}
    {σ : EuclideanSpace ℝ (Fin 1) → H} {φ : EuclideanSpace ℝ (Fin 1) × F → M}
    (hσ0 : σ 0 = a) (hσs : ContDiff ℝ ∞ σ) (hσe : IsEmbedding σ)
    (hσd : ∀ x, Injective (fderiv ℝ σ x)) (hO : IsOpen O) (hrσ : range σ = B ∩ O)
    (hφ : IsSmoothEmbedding ((𝓡 1).prod IF) I ∞ φ) (hr : range φ = X ∩ f ⁻¹' range σ)
    (hf : ∀ x z, f (φ (x, z)) = σ x) {γ : ℝ → H} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγB : γ '' Icc 0 1 ⊆ B) (hγ0 : γ 0 = a) (hN₀ : IsOpen N₀)
    (haN₀ : a ∈ N₀) (hK : K ∩ N₀ = γ '' Icc 0 1 ∩ N₀) :
    ∃ χ : H → ℝ, ContDiff ℝ ∞ χ ∧ χ a = 0 ∧ ∃ N : Set H, IsOpen N ∧ a ∈ N ∧
      (∀ b ∈ B ∩ N, (b ∈ K ↔ 0 ≤ χ b)) ∧ (∀ b ∈ B ∩ N, χ b = 0 → b = a) ∧
      (∀ p ∈ X, f p = a → ∀ V ∈ 𝓝 p, ∃ q ∈ V, q ∈ X ∧ f q ∈ N ∧ χ (f q) < 0) ∧
      ∀ p ∈ X, f p = a → MDifferentiableAt I 𝓘(ℝ, H) f p →
        mfderiv I 𝓘(ℝ, ℝ) (fun q => χ (f q)) p ≠ 0 := by
  obtain ⟨ℓ, c, hc, δ, hδ, N, hN, haN, hKN, hzero, hpar, d, hd, hder⟩ :=
    exists_side_function_G6C hσs hσe hσd hO hrσ hσ0 hγc hγi hγB hγ0 hN₀ haN₀ hK
  set e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
    with he
  set χ : H → ℝ := fun x => c * ℓ (x - a) with hχdef
  have hχs : ContDiff ℝ ∞ χ := contDiff_const.mul (ℓ.contDiff.comp (contDiff_id.sub contDiff_const))
  have hc2 : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  -- a point of `X` over `a` is `φ (0, z₀)`
  have hover : ∀ p ∈ X, f p = a → ∃ z₀, φ (0, z₀) = p := by
    intro p hp hpa
    have hpr : p ∈ range φ := by
      rw [hr]
      exact ⟨hp, ⟨0, by rw [hσ0, hpa]⟩⟩
    obtain ⟨⟨x₀, z₀⟩, rfl⟩ := hpr
    have hx₀ : x₀ = 0 := hσe.injective (by rw [← hf x₀ z₀, hpa, hσ0])
    exact ⟨z₀, by rw [hx₀]⟩
  have hφc : Continuous φ := hφ.isEmbedding.continuous
  refine ⟨χ, hχs, by simp [hχdef], N, hN, haN, hKN, hzero, ?_, ?_⟩
  · -- points on the outer side
    intro p hp hpa V hV
    obtain ⟨z₀, rfl⟩ := hover p hp hpa
    have hκc : Continuous fun t : ℝ => φ (e (-c * t), z₀) :=
      hφc.comp ((e.continuous.comp (continuous_const.mul continuous_id)).prodMk continuous_const)
    have hκ0 : φ (e (-c * 0), z₀) = φ (0, z₀) := by simp
    have hpre : (fun t : ℝ => φ (e (-c * t), z₀)) ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      hκc.continuousAt.preimage_mem_nhds (by rw [hκ0]; exact hV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    set t := min (ε / 2) (δ / 2) with htdef
    have ht0 : 0 < t := lt_min (by linarith) (by linarith)
    have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htδ : t < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hct : -c * t ∈ Ioo (-δ) δ := by
      rcases hc with rfl | rfl
      · constructor <;> linarith
      · constructor <;> linarith
    obtain ⟨hmemN, hsign⟩ := hpar (-c * t) hct
    refine ⟨φ (e (-c * t), z₀), hball ?_, ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith
    · have : φ (e (-c * t), z₀) ∈ range φ := mem_range_self _
      rw [hr] at this
      exact this.1
    · rw [hf]
      exact hmemN
    · rw [hf]
      change c * ℓ (σ (e (-c * t)) - a) < 0
      rw [hsign]
      have : c * (-c * t) = -(c * c) * t := by ring
      rw [this, hc2]
      linarith
  · -- regularity through the chart curve
    intro p hp hpa hfd h0
    obtain ⟨z₀, rfl⟩ := hover p hp hpa
    have hχd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => χ (f q)) (φ (0, z₀)) :=
      ((hχs.contMDiff (n := ∞)).mdifferentiableAt (by simp)).comp _ hfd
    have hκd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r : ℝ => φ (e r, z₀)) 0 := by
      have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 1).prod IF) (fun r : ℝ => (e r, z₀)) 0 :=
        (((e.contDiff (n := ∞)).contMDiff).mdifferentiableAt (by simp)).prodMk
          mdifferentiableAt_const
      have h2 : MDifferentiableAt ((𝓡 1).prod IF) I φ (e 0, z₀) :=
        hφ.contMDiff.mdifferentiableAt (by simp)
      exact h2.comp 0 h1
    have hκ0 : (fun r : ℝ => φ (e r, z₀)) 0 = φ (0, z₀) := by simp
    have hχd' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => χ (f q)) ((fun r : ℝ => φ (e r, z₀)) 0) := by
      rw [hκ0]
      exact hχd
    have hcomp := hχd'.hasMFDerivAt.comp 0 hκd.hasMFDerivAt
    have h0' : mfderiv I 𝓘(ℝ, ℝ) (fun q => χ (f q)) ((fun r : ℝ => φ (e r, z₀)) 0) = 0 := by
      rw [hκ0]
      exact h0
    rw [h0', ContinuousLinearMap.zero_comp] at hcomp
    have hfun : ((fun q => χ (f q)) ∘ fun r : ℝ => φ (e r, z₀)) =
        fun r => c * ℓ (σ (e r) - a) := funext fun r => by simp only [comp_apply, hf, hχdef]
    rw [hfun] at hcomp
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => c * ℓ (σ (e r) - a)) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight d) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr hder.hasFDerivAt
    have h3 := hcomp.mfderiv.symm.trans h2.mfderiv
    have h4 := congrArg (fun L => L (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ))) h3
    have h5 : ((1 : ℝ →L[ℝ] ℝ).smulRight d) (1 : ℝ) = d := by simp
    exact hd (h5.symm.trans h4.symm)

end DifferentialGeometry.Topology
