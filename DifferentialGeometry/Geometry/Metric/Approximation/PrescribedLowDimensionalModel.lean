import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalModels
import DifferentialGeometry.Geometry.Metric.Approximation.ControlledProductLimit
import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedCoordinateConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingPolynomialCovering
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false
open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GC.MetricGeometry

universe u v w

theorem exists_subsequence_prescribed_one_dimensional_models
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    {C : ℕ → Type v} [∀ i, MetricSpace (C i)] [∀ i, CompleteSpace (C i)]
    {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)]
    (p : ∀ i, X i) (c : ∀ i, C i) (z : ∀ i, Z i) {σ β : ℕ → ℝ}
    (hcurves : ∀ i, ∀ a b : C i, ∀ η : ℝ, 0 < η →
      ∃ f : unitInterval → C i, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
        eVariationOn f univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (univ : Set (C i)) ≤ 2)
    (hcomp : ∀ i, fourPointComparison 0 (univ : Set (C i)))
    (f : ∀ i, KleinerLottApprox (p i) (c i) (σ i))
    (F : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), z i)) (β i))
    (hσ : Tendsto σ atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 0)) :
    ∃ (W : Type) (mW : MetricSpace W), letI := mW
      ∃ (q : W) (χ : ℕ → ℕ), StrictMono χ ∧ ProperSpace W ∧ CompleteSpace W ∧
        fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 1 ∧
        (∀ a b : W, ∃ γ : Icc (0 : ℝ) 1 → W, Continuous γ ∧
          γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (γ s) (γ t) = dist a b * dist s t) ∧
        ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ i in atTop,
          ∃ G : KleinerLottApprox (p (χ i)) (WithLp.toLp 2 ((0 : ℝ), q)) δ,
            ∀ x : X (χ i), (G.toFun x).fst = ((F (χ i)).toFun x).fst := by
  have hR : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hcover := polynomial_covering_of_growing_local_geometry c (n := 2) (by decide)
    hcurves (κ := fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds hR
    (fun i => (dimH_mono (subset_univ _)).trans (hdim i))
    (fun i x _ => ⟨univ, isOpen_univ, hcomp i, mem_univ x⟩)
  obtain ⟨Y, mY, y, α, hα, hcY, hpY, hCconv, hXconv, _, hYcomp, hYseg⟩ :=
    exists_common_pointed_limit_of_nonnegative_models c p (n := 2) (by decide) hcurves hdim hcomp f hσ
  let := mY
  let := hcY
  let := hpY
  obtain ⟨W, mW, q, ψ, hψ, hpW, hcW, _, _, e, he, R, ε, hrad, herr, g, hclose⟩ :=
    hXconv.exists_controlled_product_limit_of_approximate_products
      (fun i => F (α i)) (hβ.comp hα.tendsto_atTop)
  let := mW
  have hdimW : dimH (univ : Set W) ≤ 1 := by
    have hh := hCconv.dimH_real_factor_le (n := 2) (by decide) (fun R hR => by
      obtain ⟨D, hD, hd⟩ := hcover R hR
      exact ⟨D, hD, fun η hη hηone => hα.tendsto_atTop.eventually (hd η hη hηone)⟩) e q
    simpa only [Nat.reduceSub, Nat.cast_one, ENNReal.ofReal_one] using hh
  refine ⟨W, mW, q, α ∘ ψ, hα.comp hψ, hpW, hcW,
    fourPointComparison_l2_product_factor hYcomp e 0, hdimW,
    e.exists_segment_l2_product_factor 0 hYseg, ?_⟩
  intro δ hδ hδone
  have hp (i : ℕ) : ((F (α (ψ i))).toFun (p (α (ψ i)))).fst = (e y).fst := by
    rw [(F (α (ψ i))).basepoint, he]
    rfl
  have hh := eventually_prescribed_kleinerLott_approximation e g hrad herr
    (fun i x => ((F (α (ψ i))).toFun x).fst) hp
    (fun S η hη => (hclose S η hη).mono fun _ hi x hx => (hi x hx).le) hδ hδone
  rw [he] at hh
  exact hh

theorem exists_prescribed_one_dimensional_model_parameter
    {e : ℝ} (he : 0 < e) (heone : e < 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < e / 10 ∧
      ∀ (X : Type u) [MetricSpace X] (p : X)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ a b : C, ∀ η : ℝ, 0 < η →
        ∃ f : unitInterval → C, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
          eVariationOn f univ < ENNReal.ofReal (dist a b + η)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (Z : Type w) [MetricSpace Z] (z : Z) (σ β : ℝ), σ ≤ a₀ → β ≤ a₀ →
        KleinerLottApprox p c σ →
        ∀ F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β,
        ∃ (W : Type) (mW : MetricSpace W), letI := mW
          ∃ q : W, ProperSpace W ∧ CompleteSpace W ∧
            fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 1 ∧
            (∀ a b : W, ∃ γ : Icc (0 : ℝ) 1 → W, Continuous γ ∧
              γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (γ s) (γ t) = dist a b * dist s t) ∧
            ∃ G : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) e,
              ∀ x : X, (G.toFun x).fst = (F.toFun x).fst := by
  classical
  let Bad (a₀ : ℝ) : Prop :=
    ∃ (X : Type u) (mX : MetricSpace X), letI := mX
      ∃ (p : X) (C : Type v) (mC : MetricSpace C), letI := mC
        ∃ (_ : CompleteSpace C) (c : C) (Z : Type w) (mZ : MetricSpace Z), letI := mZ
          ∃ (z : Z) (σ β : ℝ)
            (_ : KleinerLottApprox p c σ)
            (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β),
            σ ≤ a₀ ∧ β ≤ a₀ ∧
            (∀ a b : C, ∀ η : ℝ, 0 < η →
              ∃ f : unitInterval → C, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
                eVariationOn f univ < ENNReal.ofReal (dist a b + η)) ∧
            dimH (univ : Set C) ≤ 2 ∧ fourPointComparison 0 (univ : Set C) ∧
            ¬ ∃ (W : Type) (mW : MetricSpace W), letI := mW
              ∃ q : W, ProperSpace W ∧ CompleteSpace W ∧
                fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 1 ∧
                (∀ a b : W, ∃ γ : Icc (0 : ℝ) 1 → W, Continuous γ ∧
                  γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
                  ∀ s t, dist (γ s) (γ t) = dist a b * dist s t) ∧
                ∃ G : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) e,
                  ∀ x : X, (G.toFun x).fst = (F.toFun x).fst
  by_contra hnone
  have hbad (a₀ : ℝ) (ha : 0 < a₀) (hae : a₀ < e / 10) : Bad a₀ := by
    by_contra hb
    apply hnone
    refine ⟨a₀, ha, hae, ?_⟩
    intro X mX p C mC hc c hcurves hdim hcomp Z mZ z σ β hσ hβ f F
    by_contra hG
    exact hb ⟨X, mX, p, C, mC, hc, c, Z, mZ, z, σ, β, f, F,
      hσ, hβ, hcurves, hdim, hcomp, hG⟩
  let η : ℕ → ℝ := fun i => min (e / 20) (1 / ((i : ℝ) + 20))
  have hηpos (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hηsmall (i : ℕ) : η i < e / 10 := (min_le_left _ _).trans_lt (by linarith)
  have hηzero : Tendsto η atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 20) atTop atTop :=
      tendsto_atTop_add_const_right atTop (20 : ℝ) tendsto_natCast_atTop_atTop
    have hi : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 20)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
    exact squeeze_zero (fun i => (hηpos i).le) (fun _ => min_le_right _ _) hi
  choose X mX p C mC hc c Z mZ z σ β f F hση hβη hcurves hdim hcomp hbadG using
    fun i => hbad (η i) (hηpos i) (hηsmall i)
  let : ∀ i, MetricSpace (X i) := mX
  let : ∀ i, MetricSpace (C i) := mC
  let : ∀ i, CompleteSpace (C i) := hc
  let : ∀ i, MetricSpace (Z i) := mZ
  have hσzero : Tendsto σ atTop (𝓝 0) := squeeze_zero (fun i => (f i).error_pos.le) hση hηzero
  have hβzero : Tendsto β atTop (𝓝 0) := squeeze_zero (fun i => (F i).error_pos.le) hβη hηzero
  obtain ⟨W, mW, q, χ, _, hpW, hcW, hcompW, hdimW, hsegW, hG⟩ :=
    exists_subsequence_prescribed_one_dimensional_models p c z hcurves hdim hcomp f F hσzero hβzero
  let := mW
  obtain ⟨i, G, hGcoord⟩ := (hG e he heone).exists
  exact hbadG (χ i) ⟨W, mW, q, hpW, hcW, hcompW, hdimW, hsegW, G, hGcoord⟩

end GC.MetricGeometry
