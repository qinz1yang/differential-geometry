import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Quotient
import DifferentialGeometry.Topology.GroupAction.CompactLifting
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded

open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.AsymptoticRays

open Filter (Tendsto atTop)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open Busemann (busemann horosphere)

variable {n : ℕ}

private theorem cosh_dist_rayTo_rayTo_of_busemann_eq
    (x y : HUpper n) (ξ : BoundaryH n) (hxy : busemann ξ x = busemann ξ y) (t : ℝ) :
    Real.cosh (dist (rayTo x ξ t) (rayTo y ξ t)) =
      1 + (Real.cosh (dist x y) - 1) * Real.exp (-(2 * t)) := by
  have hpair : Hyperbolic.lorB x.val ξ.val = Hyperbolic.lorB y.val ξ.val := by
    have h := congrArg Real.exp hxy
    change Real.exp (Real.log (-Hyperbolic.lorB x.val ξ.val)) =
      Real.exp (Real.log (-Hyperbolic.lorB y.val ξ.val)) at h
    rw [Real.exp_log (Busemann.neg_lorB_upper_boundary_pos x ξ),
      Real.exp_log (Busemann.neg_lorB_upper_boundary_pos y ξ)] at h
    exact neg_injective h
  rw [cosh_dist_rayTo_rayTo, hpair,
    div_self (lorB_hUpper_boundary_neg y ξ).ne]
  have hE : (Real.cosh t - Real.sinh t) ^ 2 = Real.exp (-(2 * t)) := by
    rw [cosh_sub_sinh, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hE, HyperbolicConvexity.cosh_dist]
  ring

theorem tendsto_ediam_image_rayTo_of_isBounded
    (ξ : BoundaryH n) (c : ℝ) {S : Set (HUpper n)}
    (hS : Bornology.IsBounded S) (hhor : S ⊆ horosphere ξ c) :
    Tendsto (fun t : ℝ => Metric.ediam ((fun x => rayTo x ξ t) '' S)) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hS
  let C := max 0 D
  have hC : 0 ≤ C := le_max_left _ _
  have hbound : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ C := by
    intro x hx y hy
    exact (hD hx hy).trans (le_max_right _ _)
  let R : ℝ → ℝ := fun t => Real.arcosh
    (1 + (Real.cosh C - 1) * Real.exp (-(2 * t)))
  have harg1 (t : ℝ) : 1 ≤ 1 + (Real.cosh C - 1) * Real.exp (-(2 * t)) := by
    have hmul := mul_nonneg (sub_nonneg.mpr (Real.one_le_cosh C)) (Real.exp_pos (-(2 * t))).le
    linarith only [hmul]
  have hE : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop (by norm_num))
  have harg : Tendsto (fun t : ℝ => 1 + (Real.cosh C - 1) * Real.exp (-(2 * t)))
      atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (hE.const_mul (Real.cosh C - 1)).const_add 1
  have harcosh : Tendsto Real.arcosh (𝓝[Set.Ici 1] (1 : ℝ)) (𝓝 0) := by
    have hh := Real.continuousOn_arcosh (1 : ℝ) (by simp only [Set.mem_Ici, le_refl])
    change Tendsto Real.arcosh (𝓝[Set.Ici 1] (1 : ℝ)) (𝓝 (Real.arcosh 1)) at hh
    simpa only [Real.arcosh_zero] using hh
  have hR : Tendsto R atTop (𝓝 0) :=
    harcosh.comp (tendsto_nhdsWithin_iff.mpr
      ⟨harg, Filter.Eventually.of_forall harg1⟩)
  have hdist (t : ℝ) (x : HUpper n) (hx : x ∈ S) (y : HUpper n) (hy : y ∈ S) :
      dist (rayTo x ξ t) (rayTo y ξ t) ≤ R t := by
    have hxy : busemann ξ x = busemann ξ y := (hhor hx).trans (hhor hy).symm
    have hc : Real.cosh (dist x y) ≤ Real.cosh C :=
      Real.cosh_le_cosh.mpr (by
        simpa only [abs_of_nonneg dist_nonneg, abs_of_nonneg hC] using hbound x hx y hy)
    have hcosh : Real.cosh (dist (rayTo x ξ t) (rayTo y ξ t)) ≤
        1 + (Real.cosh C - 1) * Real.exp (-(2 * t)) := by
      rw [cosh_dist_rayTo_rayTo_of_busemann_eq x y ξ hxy t]
      exact add_le_add (le_refl (1 : ℝ))
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hc 1) (Real.exp_pos _).le)
    calc
      dist (rayTo x ξ t) (rayTo y ξ t) =
          Real.arcosh (Real.cosh (dist (rayTo x ξ t) (rayTo y ξ t))) :=
        (Real.arcosh_cosh dist_nonneg).symm
      _ ≤ R t := (Real.arcosh_le_arcosh (Real.cosh_pos _) (lt_of_lt_of_le zero_lt_one (harg1 t))).mpr hcosh
  have hdiam (t : ℝ) : Metric.ediam ((fun x => rayTo x ξ t) '' S) ≤ ENNReal.ofReal (R t) := by
    apply Metric.ediam_le_of_forall_dist_le
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hdist t x hx y hy
  have hRE : Tendsto (fun t => ENNReal.ofReal (R t)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hR
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hRE ε hε] with t ht
  exact (hdiam t).trans ht

end DifferentialGeometry.AsymptoticRays

namespace DifferentialGeometry.HorosphereProjection

open Filter (Tendsto atTop)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open ProjectiveOrthogonalGroup (PO)
open HyperbolicAction (poMulAction)
open Busemann (busemann horosphere)
open BusemannCocycle (poConfFactor)
open AsymptoticRays (rayTo)

variable {n : ℕ} {M : Type*} [PseudoEMetricSpace M]

theorem tendsto_ediam_image_horosphere
    (hn : 1 ≤ n) (P : Subgroup (PO n 1)) (ξ : BoundaryH n) (c : ℝ)
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1)
    (hcompact : IsCompact ((Quotient.mk
      (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))) '' horosphere ξ c))
    (p : HUpper n → M) {L : ℝ≥0} (hp : LipschitzWith L p)
    (hinv : ∀ (γ : P) (x : HUpper n), p ((poMulAction hn).smul (γ : PO n 1) x) = p x) :
    Tendsto (fun t : ℝ => Metric.ediam (p '' horosphere ξ (c - t))) atTop (𝓝 0) := by
  let _ := EquivariantMap.subAction hn P
  let _ : ContinuousConstSMul P (HUpper n) :=
    ⟨fun γ => (ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id)⟩
  obtain ⟨S, hS, hrep⟩ := MulAction.exists_compact_representatives hcompact
  let C := S ∩ horosphere ξ c
  have hclosed : IsClosed (horosphere ξ c) :=
    isClosed_eq (continuous_busemann ξ) continuous_const
  have hC : IsCompact C := hS.inter_right hclosed
  have hCsub : C ⊆ horosphere ξ c := Set.inter_subset_right
  have hrepC (x : HUpper n) (hx : x ∈ horosphere ξ c) :
      ∃ γ : P, (poMulAction hn).smul (γ : PO n 1) x ∈ C := by
    obtain ⟨γ, hγ⟩ := hrep x (Set.mem_image_of_mem (Quotient.mk _) hx)
    refine ⟨γ, hγ, ?_⟩
    have hb := BusemannCocycle.po_busemann_smul hn (γ : PO n 1) ξ x
    have he : busemann ξ ((poMulAction hn).smul (γ : PO n 1) x) = busemann ξ x := by
      simpa only [(hhor γ).1, (hhor γ).2, Real.log_one, sub_zero] using hb
    exact he.trans hx
  have himage (t : ℝ) : p '' horosphere ξ (c - t) =
      p '' ((fun x => rayTo x ξ t) '' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let x₀ := rayTo x ξ (-t)
      have hx₀ : x₀ ∈ horosphere ξ c := by
        change busemann ξ (rayTo x ξ (-t)) = c
        rw [busemann_rayTo, show busemann ξ x = c - t from hx]
        ring
      obtain ⟨γ, hγ⟩ := hrepC x₀ hx₀
      refine ⟨rayTo ((poMulAction hn).smul (γ : PO n 1) x₀) ξ t,
        ⟨(poMulAction hn).smul (γ : PO n 1) x₀, hγ, rfl⟩, ?_⟩
      have he := BoundaryExtension.po_smul_rayTo hn (γ : PO n 1) x₀ ξ t
      change (poMulAction hn).smul (γ : PO n 1) (rayTo x₀ ξ t) =
        rayTo ((poMulAction hn).smul (γ : PO n 1) x₀)
          ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ) t at he
      rw [(hhor γ).1] at he
      rw [← he, hinv]
      dsimp only [x₀]
      rw [rayTo_add, neg_add_cancel, AsymptoticRays.rayTo_zero]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨rayTo x ξ t, ?_, rfl⟩
      change busemann ξ (rayTo x ξ t) = c - t
      rw [busemann_rayTo, show busemann ξ x = c from hCsub hx]
  have hlim := AsymptoticRays.tendsto_ediam_image_rayTo_of_isBounded ξ c hC.isBounded hCsub
  have hlimL : Tendsto
      (fun t : ℝ => (L : ℝ≥0∞) * Metric.ediam ((fun x => rayTo x ξ t) '' C))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (ENNReal.coe_ne_top : (L : ℝ≥0∞) ≠ ⊤))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hlimL ε hε] with t ht
  rw [himage]
  exact (hp.ediam_image_le _).trans ht

end DifferentialGeometry.HorosphereProjection
