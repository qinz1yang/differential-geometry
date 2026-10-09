import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalOrientedProduct
import DifferentialGeometry.Geometry.Metric.Approximation.ScalarPrescribedCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialCalibration

/-!
# Compactness with the original centered radial coordinate

Long opposite anchors yield a product limit. Calibration is imposed on their actual prefixes,
so AC52 prescribes the original center distance rather than the distance to a strainer anchor.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u

variable {A : ℕ → Type u} [∀ i, MetricSpace (A i)] [∀ i, CompleteSpace (A i)]

theorem exists_subsequence_original_radial_splittings
    (o p aPlus aMinus : ∀ i, A i) {σ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (ball (o i) ((σ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (o i) ((σ i)⁻¹),
      ∃ Ω : Set (A i), IsOpen Ω ∧ fourPointComparison (σ i) Ω ∧ z ∈ Ω)
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (hp : ∀ i, dist (o i) (aPlus i) = (σ i)⁻¹)
    (hm : ∀ i, dist (o i) (aMinus i) = (σ i)⁻¹)
    (hopposite : ∀ i, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (o i) (aPlus i)) (dist (o i) (aMinus i)) (dist (aPlus i) (aMinus i)))
    (hrad : ∀ i w, dist (o i) w + dist w (aPlus i) = dist (o i) (aPlus i) →
      dist (o i) w - σ i * dist (o i) w ≤ dist (p i) w - dist (p i) (o i))
    (hinward : ∀ i, dist (o i) (aMinus i) + dist (aMinus i) (p i) = dist (o i) (p i)) :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ z : Z, ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ i in atTop,
          ∃ F : KleinerLottApprox (o (χ i))
            (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) β,
            ∀ x : A (χ i), (F.toFun x).fst =
              WithLp.toLp 2 (Function.const (Fin 1)
                (dist (p (χ i)) x - dist (p (χ i)) (o (χ i)))) := by
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun i => (σ i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hwithin
  obtain ⟨Y, mY, y, φ, hφ, hcomplete, hproper, hpointed, hrest⟩ :=
    exists_pointed_limit_of_growing_local_geometry o hn hcurves
      (fun i => (hσpos i).le) hσ hL hdim hlocal
  let := mY
  let := hcomplete
  let := hproper
  obtain ⟨hcomp, hsegments, hExcess, qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0,
    hqPlusEnd, hqMinusEnd, ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase,
    halign, hcal, γ, hγ, hγ0, hconv, hangle, Z, mZ, z, e, he0, haxes,
    hcoord, hbuse, hclose, hZproper, hZcomplete, hZcomp, hZsegments⟩ :=
    hpointed.exists_oriented_product_of_reciprocal_local_geometry
      (fun i => hcurves (φ i)) (fun i => hdim (φ i)) (fun i => hlocal (φ i))
      (fun i => Function.const (Fin 1) (aPlus (φ i)))
      (fun i => Function.const (Fin 1) (aMinus (φ i)))
      (fun i => hσpos (φ i)) (hσ.comp hφ.tendsto_atTop)
      (fun i => Function.const (Fin 1) (hp (φ i)))
      (fun i => Function.const (Fin 1) (hm (φ i)))
      (fun j => Eventually.of_forall fun i => hopposite (φ i))
      (fun j l hjl => absurd (Subsingleton.elim j l) hjl)
      (fun j l hjl => absurd (Subsingleton.elim j l) hjl)
  let := mZ
  have hγbase : γ 0 0 = y := hγ0 0
  subst y
  have hχ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hσχ : Tendsto (fun i => σ (φ (ψ i))) atTop (𝓝 0) := hσ.comp hχ.tendsto_atTop
  have hradial := eventually_original_radial_error_lt
    (lineSplitting hcomp (hγ 0) hsegments)
    (lineSplitting_apply_line hcomp (hγ 0) hsegments)
    f hR hε (fun i => p (φ (ψ i)))
    (fun T hT η hη => by
      have herror : Tendsto (fun i => σ (φ (ψ i)) * T) atTop (𝓝 0) := by
        simpa only [zero_mul] using hσχ.mul_const T
      filter_upwards [hconv T η hη,
        herror.eventually (eventually_lt_nhds hη)] with i hi herr
      let t : Icc (0 : ℝ) ((σ (φ (ψ i)))⁻¹) := ⟨T, hT.le, (hi.2 0).1⟩
      let tp : Icc (-((σ (φ (ψ i)))⁻¹)) ((σ (φ (ψ i)))⁻¹) :=
        ⟨T, by linarith [inv_pos.mpr (hσpos (φ (ψ i)))], t.property.2⟩
      let tm : Icc (-((σ (φ (ψ i)))⁻¹)) ((σ (φ (ψ i)))⁻¹) :=
        ⟨-T, by linarith [t.property.2], by linarith [hT, inv_pos.mpr (hσpos (φ (ψ i)))]⟩
      have hdistp : dist (Q i 0 tp) (o (φ (ψ i))) = T := by
        rw [(halign i 0 t).1]
        rw [← hqPlus0 (ψ i) 0, (hqPlus (ψ i) 0).dist_eq]
        simp only [Subtype.dist_eq, Real.dist_eq, sub_zero]
        change |T| = T
        exact abs_of_pos hT
      have hdistm : dist (Q i 0 tm) (o (φ (ψ i))) = T := by
        rw [(halign i 0 t).2]
        rw [← hqMinus0 (ψ i) 0, (hqMinus (ψ i) 0).dist_eq]
        simp only [Subtype.dist_eq, Real.dist_eq, sub_zero]
        change |T| = T
        exact abs_of_pos hT
      have haddp : dist (o (φ (ψ i))) (Q i 0 tp) + dist (Q i 0 tp) (aPlus (φ (ψ i))) =
          dist (o (φ (ψ i))) (aPlus (φ (ψ i))) := by
        rw [dist_comm, hdistp, hp]
        have hlo : T ≤ (σ (φ (ψ i)))⁻¹ -
            dist (Q i 0 tp) (aPlus (φ (ψ i))) := (hcal i 0 t).1
        have hhi : (σ (φ (ψ i)))⁻¹ -
            dist (Q i 0 tp) (aPlus (φ (ψ i))) ≤ T := (hcal i 0 t).2.1
        linarith
      have haddm : dist (o (φ (ψ i))) (Q i 0 tm) + dist (Q i 0 tm) (aMinus (φ (ψ i))) =
          dist (o (φ (ψ i))) (aMinus (φ (ψ i))) := by
        have hend : qMinus (ψ i) 0
            ⟨(σ (φ (ψ i)))⁻¹, (inv_pos.mpr (hσpos (φ (ψ i)))).le, le_rfl⟩ =
            aMinus (φ (ψ i)) := hqMinusEnd (ψ i) 0
        rw [(halign i 0 t).2, ← hend, ← hqMinus0 (ψ i) 0]
        rw [(hqMinus (ψ i) 0).dist_eq, (hqMinus (ψ i) 0).dist_eq,
          (hqMinus (ψ i) 0).dist_eq]
        change |0 - T| + |T - (σ (φ (ψ i)))⁻¹| = |0 - (σ (φ (ψ i)))⁻¹|
        rw [abs_of_nonpos (by linarith : (0 : ℝ) - T ≤ 0),
          abs_of_nonpos (by linarith [t.property.2] : T - (σ (φ (ψ i)))⁻¹ ≤ 0),
          abs_of_nonpos (by linarith [inv_pos.mpr (hσpos (φ (ψ i)))] :
            (0 : ℝ) - (σ (φ (ψ i)))⁻¹ ≤ 0)]
        ring
      have hminus : dist (p (φ (ψ i))) (Q i 0 tm) - dist (p (φ (ψ i))) (o (φ (ψ i))) = -T := by
        have htri := dist_triangle (Q i 0 tm) (aMinus (φ (ψ i))) (p (φ (ψ i)))
        have htri' := dist_triangle (o (φ (ψ i))) (Q i 0 tm) (p (φ (ψ i)))
        have hin := hinward (φ (ψ i))
        rw [dist_comm (o (φ (ψ i))) (Q i 0 tm), hdistm] at haddm htri'
        have heq : dist (Q i 0 tm) (p (φ (ψ i))) -
            dist (o (φ (ψ i))) (p (φ (ψ i))) = -T := by linarith
        simpa only [dist_comm (p (φ (ψ i))) (Q i 0 tm),
          dist_comm (p (φ (ψ i))) (o (φ (ψ i)))] using heq
      have hpR : dist (Q i 0 tp) (o (φ (ψ i))) ≤ R i := hdistp ▸ hi.1
      have hmR : dist (Q i 0 tm) (o (φ (ψ i))) ≤ R i := hdistm ▸ hi.1
      refine ⟨⟨Q i 0 tp, hpR⟩, ⟨Q i 0 tm, hmR⟩, ?_, ?_, ?_, ?_⟩
      · have hh := hrad (φ (ψ i)) (Q i 0 tp) haddp
        rw [dist_comm (o (φ (ψ i))), hdistp] at hh
        linarith
      · rw [hminus]
        linarith
      · exact ((hi.2 0).2 tp (by dsimp [tp]; rw [abs_of_pos hT]) hpR).le
      · exact ((hi.2 0).2 tm (by dsimp [tm]; rw [abs_neg, abs_of_pos hT]) hmR).le)
  refine ⟨φ ∘ ψ, hχ, Z, mZ, z, ?_⟩
  intro β hβ hβone
  have hcloseRad : ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ j, ∀ x : BallCarrier (o (φ (ψ i))) (R i), dist x.val (o (φ (ψ i))) ≤ S →
        |dist (p (φ (ψ i))) x.val - dist (p (φ (ψ i))) (o (φ (ψ i))) -
          (e ((f i).toFun x)).fst j| < η := by
    intro S hS η hη
    filter_upwards [hradial S hS η hη] with i hi
    intro j x hx
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    subst j
    simpa only [lineSplitting_fst, hcoord] using hi.2 x hx
  have hpRad : ∀ i, WithLp.toLp 2 (Function.const (Fin 1)
      (dist (p (φ (ψ i))) (o (φ (ψ i))) - dist (p (φ (ψ i))) (o (φ (ψ i))))) =
      (e (γ 0 0)).fst := by
    intro i
    rw [he0]
    ext j
    change dist (p (φ (ψ i))) (o (φ (ψ i))) -
      dist (p (φ (ψ i))) (o (φ (ψ i))) = 0
    exact sub_self _
  have h := eventually_prescribed_kleinerLott_approximation_of_component_convergence
    e f hR hε (fun i x => WithLp.toLp 2 (Function.const (Fin 1)
      (dist (p (φ (ψ i))) x - dist (p (φ (ψ i))) (o (φ (ψ i)))))) hpRad hcloseRad hβ hβone
  rw [he0] at h
  exact h

end GC.MetricGeometry
