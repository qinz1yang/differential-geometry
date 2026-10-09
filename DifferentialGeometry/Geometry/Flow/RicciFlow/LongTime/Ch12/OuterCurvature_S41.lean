import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterCurvatureBridge_S41
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceRadius_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallInputs_S29
import DifferentialGeometry.Geometry.Curvature.SectionalOrthonormalization
import DifferentialGeometry.Geometry.Curvature.ConstantSectional

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- (S41 bridge 3) At every point `z` of the doubled buffer ball, a smooth metric `q` on the model
with the pullback germ of `gb` at `z`, whose C^j distance (`j ≤ 2`) to `h` is `< accuracy t`
(from `buffer_error`), and with the same sectional lower bounds as `gb` at `φ z`. -/
theorem bufferedMap_curvature_bridge_S41 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (hgb : ∀ w, localPullInner (I := 𝓡 3) (J := 𝓡 3) gb (B.map i t ht) w =
      (t⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
        (B.map i t ht) w)
    (z : (B.model i).Carrier)
    (hz : z ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (2 * (B.accuracy t)⁻¹))
    (hk : 2 ≤ max K ⌈(B.accuracy t)⁻¹⌉₊) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) (B.model i).Carrier,
      (∀ j : ℕ, j ≤ 2 → metricDerivNorm j q (B.model i).metric (B.model i).metric z <
        B.accuracy t) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔
        SectionalBoundedBelowAt gb (B.map i t ht z) κ := by
  have hzd : z ∈ B.domain i t := B.buffer_domain i t ht hz
  obtain ⟨q, hgerm, hiff⟩ := bufferedMap_pullbackGerm_S41 B i t ht gb z hzd
  refine ⟨q, fun j hj => ?_, hiff⟩
  have hzint : (𝓡 3).IsInteriorPoint z := BoundarylessManifold.isInteriorPoint
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) (2 + 1 : ℕ) (B.map i t ht) z :=
    ((B.smooth i t ht).contMDiffAt ((B.domain i t).isOpen.mem_nhds hzd)).of_le (by simp)
  have key := DifferentialGeometry.Geometry.metricDerivNorm_eq_raw_pullbackError_of_map_jets
    gb (B.model i).metric q (f := B.map i t ht) (h := B.map i t ht) (p := z) (n := 2)
    hzint BoundarylessManifold.isInteriorPoint rfl hf hf (fun _ _ => rfl) hgerm j hj
  have herr := B.buffer_error i t ht j (hj.trans hk) z hz
  simp only [← hgb] at herr
  rw [key]
  exact herr

/-- An orthonormal pair at a point of a 3-dimensional model. -/
theorem exists_orthonormal_pair_model_S41 (H : FiniteVolumeHyperbolicModel.{u})
    (y : H.Carrier) :
    ∃ u v : TangentSpace (𝓡 3) y, H.metric.inner y u u = 1 ∧ H.metric.inner y v v = 1 ∧
      H.metric.inner y u v = 0 := by
  let v : TangentSpace (𝓡 3) y := EuclideanSpace.single 0 1
  let w : TangentSpace (𝓡 3) y := EuclideanSpace.single 1 1
  have hli : LinearIndependent ℝ ![v, w] := by
    have h := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
    have hinj : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by decide
    have h2 := h.comp (![0, 1] : Fin 2 → Fin 3) hinj
    have heq : (![v, w] : Fin 2 → TangentSpace (𝓡 3) y) =
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis ∘ (![0, 1] : Fin 2 → Fin 3) := by
      funext i
      fin_cases i
      · exact (EuclideanSpace.basisFun_apply (Fin 3) ℝ 0).symm
      · exact (EuclideanSpace.basisFun_apply (Fin 3) ℝ 1).symm
    rw [heq]
    exact h2
  obtain ⟨u, q, hu, hq, huq, -⟩ := DifferentialGeometry.Geometry.exists_orthonormal_pair_sectional_quotient H.metric y v w hli
  exact ⟨u, q, hu, hq, huq⟩

/-- **(G1, hUp)** For late `t` and every `y ∈ B(x_i, n)`, some plane at `φ y` has
`sec ḡ_t < -1/8` (the model has curvature `-1/4`; the buffer error is `< accuracy t`). -/
theorem hUp_S41 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) :
    ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) := by
  obtain ⟨T₀, -, hT₀⟩ := accuracy_inv_large_S29 B 10000
  refine ⟨T₀, fun t ht hT i y hy => ?_⟩
  have hn : (10000 : ℝ) ≤ (B.accuracy t)⁻¹ := hT₀ t hT
  have hpos : 0 < B.accuracy t := B.accuracy_pos t ht
  have hacc : B.accuracy t ≤ 1 / 10000 := by
    rw [le_inv_comm₀ (by norm_num) hpos] at hn
    simpa using hn
  have hceil : 2 ≤ ⌈(B.accuracy t)⁻¹⌉₊ := by
    have h2 : (2 : ℝ) ≤ ⌈(B.accuracy t)⁻¹⌉₊ := (by linarith : (2 : ℝ) ≤ (B.accuracy t)⁻¹).trans
      (Nat.le_ceil _)
    exact_mod_cast h2
  have hk : 2 ≤ max K ⌈(B.accuracy t)⁻¹⌉₊ := hceil.trans (le_max_right _ _)
  have hy2 : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith) hy
  obtain ⟨q, hq, hiff⟩ := bufferedMap_curvature_bridge_S41 B i t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    y hy2 hk
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair_model_S41 (B.model i) y
  have href : ∀ a b : TangentSpace (𝓡 3) y,
      metricRm04StandardAt (B.model i).metric y a b b a =
        -(1 / 4 : ℝ) * ((B.model i).metric.inner y a a * (B.model i).metric.inner y b b -
          (B.model i).metric.inner y a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 (B.model i) y a b]; ring
  have hcurv : metricRm04StandardAt (B.model i).metric y u v v u ≤ -(1 / 4 : ℝ) := by
    rw [href u v, hu, hv, huv]; norm_num
  have hmodel : Real.sqrt ((B.model i).metric.inner y
      (riemannOp (LeviCivita (B.model i).metric) y u v v)
      (riemannOp (LeviCivita (B.model i).metric) y u v v)) ≤ 2 :=
    (sqrt_inner_riemannOp_self_eq_abs_of_constant_sectional_numerator
      (B.model i).metric y (-(1 / 4 : ℝ)) href u v hu hv huv).trans_le (by norm_num)
  have hnot := not_sectionalBoundedBelowAt_neg_one_eighth_of_small_metric_derivatives q
    (B.model i).metric y (eps := B.accuracy t) hacc (fun j hj => (hq j hj).le) u v hu hv hcurv
    hmodel
  exact fun hs => hnot ((hiff _).mpr hs)

end GC.LongTime.Ch12
