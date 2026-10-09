import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Metric.Approximation.VaryingKleinerLottConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateProductLimit
import DifferentialGeometry.Geometry.Metric.Approximation.FactorDimension

set_option autoImplicit false
open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w

theorem exists_common_pointed_limit_of_nonnegative_models
    {C : ℕ → Type u} [∀ i, MetricSpace (C i)] [∀ i, CompleteSpace (C i)]
    {Z : ℕ → Type v} [∀ i, MetricSpace (Z i)]
    (c : ∀ i, C i) (z : ∀ i, Z i) {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : C i, ∀ η : ℝ, 0 < η →
      ∃ f : unitInterval → C i, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
        eVariationOn f univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (univ : Set (C i)) ≤ n)
    (hcomp : ∀ i, fourPointComparison 0 (univ : Set (C i)))
    {σ : ℕ → ℝ} (f : ∀ i, KleinerLottApprox (z i) (c i) (σ i))
    (hσ : Tendsto σ atTop (𝓝 0)) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (q : Y) (a : ℕ → ℕ), StrictMono a ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => c (a i)) q ∧
        PointedGHConverges (fun i => z (a i)) q ∧
        dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∀ x y : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
          γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (γ s) (γ t) = dist x y * dist s t := by
  have hR : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  obtain ⟨Y, mY, q, a, ha, hcY, hpY, hconv, hdimY, hcompY, hseg, _, _⟩ :=
    exists_pointed_limit_of_growing_local_geometry c hn hcurves
      (κ := fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds hR
      (fun i => (dimH_mono (subset_univ _)).trans (hdim i))
      (fun i x _ => ⟨univ, isOpen_univ, hcomp i, mem_univ x⟩)
  let := mY
  have hzconv := (pointedGHConverges_iff_of_kleinerLott_sequence
    (fun i => f (a i)) (hσ.comp ha.tendsto_atTop)).mpr hconv
  exact ⟨Y, mY, q, a, ha, hcY, hpY, hconv, hzconv, hdimY, hcompY, hseg⟩

theorem exists_no_higher_rank_splitting_parameter {n k : ℕ} (hn : 1 ≤ n) (hnk : n < k) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ n → fourPointComparison 0 (univ : Set C) →
      ∀ (A : Type w) [MetricSpace A] (a : A) (σ β : ℝ), σ ≤ η → β ≤ η →
        KleinerLottApprox z c σ →
        KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a)) β → False := by
  classical
  let Bad (η : ℝ) : Prop :=
    ∃ (Z : Type u) (mZ : MetricSpace Z), letI := mZ
      ∃ (z : Z) (C : Type v) (mC : MetricSpace C), letI := mC
        ∃ (_ : CompleteSpace C) (c : C) (A : Type w) (mA : MetricSpace A), letI := mA
          ∃ (a : A) (σ β : ℝ)
            (_ : KleinerLottApprox z c σ)
            (_ : KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a)) β),
            σ ≤ η ∧ β ≤ η ∧
            (∀ x y : C, ∀ e : ℝ, 0 < e →
              ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
                eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) ∧
            dimH (univ : Set C) ≤ n ∧ fourPointComparison 0 (univ : Set C)
  by_contra hnone
  have hbad (η : ℝ) (hη : 0 < η) (hηsmall : η < 1 / 10) : Bad η := by
    by_contra hb
    apply hnone
    refine ⟨η, hη, hηsmall, ?_⟩
    intro Z mZ z C mC hc c hcurves hdim hcomp A mA a σ β hσ hβ f φ
    exact hb ⟨Z, mZ, z, C, mC, hc, c, A, mA, a, σ, β, f, φ,
      hσ, hβ, hcurves, hdim, hcomp⟩
  let η : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 20)
  have hηpos (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hηsmall (i : ℕ) : η i < 1 / 10 := by
    dsimp [η]
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hηzero : Tendsto η atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 20) atTop atTop :=
      tendsto_atTop_add_const_right atTop (20 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [η, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  choose Z mZ z C mC hc c A mA a σ β f φ hση hβη hcurves hdim hcomp using
    fun i => hbad (η i) (hηpos i) (hηsmall i)
  let : ∀ i, MetricSpace (Z i) := mZ
  let : ∀ i, MetricSpace (C i) := mC
  let : ∀ i, CompleteSpace (C i) := hc
  let : ∀ i, MetricSpace (A i) := mA
  have hσzero : Tendsto σ atTop (𝓝 0) := squeeze_zero (fun i => (f i).error_pos.le) hση hηzero
  have hβzero : Tendsto β atTop (𝓝 0) := squeeze_zero (fun i => (φ i).error_pos.le) hβη hηzero
  obtain ⟨Y, mY, q, α, hα, hcY, hpY, _, hzconv, hdimY, _, _⟩ :=
    exists_common_pointed_limit_of_nonnegative_models c z hn hcurves hdim hcomp f hσzero
  let := mY
  let := hcY
  let := hpY
  obtain ⟨W, mW, w, _, _, _, _, _, _, e, _⟩ :=
    hzconv.exists_product_isometry_of_approximate_products
      (fun i => φ (α i)) (hβzero.comp hα.tendsto_atTop)
  let := mW
  have hkn := (e.euclidean_rank_le_dimH w).trans hdimY
  exact (Nat.not_le.mpr hnk) (by exact_mod_cast hkn)

end GC.MetricGeometry
