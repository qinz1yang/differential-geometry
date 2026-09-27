import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Attachment.ChartMap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.ActiveAtoms

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))

theorem IntrinsicBallChart.chartMap_apply_transition
    (i j : ι) (k : ℕ) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
    ∀ (z : U) (h : near j i = true), J ⟨(j, i), h⟩ z ∈ U →
      D.chartMap i (fun w : U => (c i k).hom w) (D.toGlueData.ι j z) =
        (c i k).hom (J ⟨(j, i), h⟩ z) := by
  intro D U hne z h hz
  let _ := hne
  exact D.chartMap_apply_overlap j i (fun w : U => (c i k).hom w) ⟨z, h, hz⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))



theorem IntrinsicBallChart.eventually_chart_active_atoms [Fintype ι] :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    ∀ (j : ι) (a : E) {r : ℝ} (hr : 0 < r)
      (hball : ∀ _k, Metric.ball a r ⊆ Metric.ball (0 : E) ρ)
      (weights : E → ι → ℝ) (xi : ℕ → E → ι → E),
      CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
        (fun k z => (weights z, xi k z)) (fun z => (weights z, fun _ => z - a)) →
      (∀ z : U, ∀ i, weights z i ≠ 0 →
        ∃ h : near j i = true, J ⟨(j, i), h⟩ z ∈ U) →
      (∀ᶠ k in atTop, ∀ z : U, ∀ i (h : near j i = true), weights z i ≠ 0 →
        xi k z i = -a + (c j k).hom.symm ((c i k).hom (J ⟨(j, i), h⟩ z))) →
      ∀ K : Set E, IsCompact K → K ⊆ U → MapsTo (fun z : E => z - a) K (Metric.ball 0 r) →
      ∀ᶠ k in atTop, ∀ (z : U), (z : E) ∈ K → ∀ i, weights z i ≠ 0 →
        letI : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
        let nc := (c j k).toNormalBallChart (g k) (hEnorm k) (x j k) hρ
        let cc := nc.recenter a hr (hball k)
        xi k z i ∈ Metric.ball (0 : E) r ∧
        cc.hom (xi k z i) = D.chartMap i (fun w : U => (c i k).hom w) (D.toGlueData.ι j z) := by
  intro D U j a r hr hball weights xi hcfg hactive hxi K hK hKU hcenter
  classical
  let nc := fun k => (c j k).toNormalBallChart (g k) (hEnorm k) (x j k) hρ
  let atom : ∀ k, E → ι → M k := fun k z i =>
    letI : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
    if hz : z ∈ U then D.chartMap i (fun w : U => (c i k).hom w) (D.toGlueData.ι j ⟨z, hz⟩)
      else x i k
  have hatom (k : ℕ) (z : U) (i : ι) (hi : weights z i ≠ 0) :
      ∃ hji : near j i = true, J ⟨(j, i), hji⟩ z ∈ U ∧
        atom k z i = (c i k).hom (J ⟨(j, i), hji⟩ z) := by
    obtain ⟨hji, hJi⟩ := hactive z i hi
    refine ⟨hji, hJi, ?_⟩
    let : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
    have hchange : atom k z i = D.chartMap i (fun w : U => (c i k).hom w)
        (D.toGlueData.ι j z) := by
      exact dif_pos z.property
    exact hchange.trans (IntrinsicBallChart.chartMap_apply_transition
      g hEnorm x hρ c near hclass J hcont hconv i j k z hji hJi)
  have htarget : ∀ᶠ k in atTop, ∀ z ∈ K, ∀ i, weights z i ≠ 0 →
      atom k z i ∈ (nc k).hom.target := by
    have h := IntrinsicBallChart.eventually_mapsTo_target_of_near
      g hEnorm x hρ (s := ρ / 8) (by linarith) c near j
      (fun i => (hclass j i).mono fun k hk => hk.1)
    filter_upwards [h] with k hk z hz i hi
    obtain ⟨hji, hJi, heq⟩ := hatom k ⟨z, hKU hz⟩ i hi
    exact heq.symm ▸ hk i hji hJi
  have hcoords : ∀ᶠ k in atTop, ∀ z ∈ K, ∀ i, weights z i ≠ 0 →
      xi k z i = -a + (nc k).inv (atom k z i) := by
    filter_upwards [hxi] with k hk z hz i hi
    obtain ⟨hji, hJi, heq⟩ := hatom k ⟨z, hKU hz⟩ i hi
    exact (hk ⟨z, hKU hz⟩ i hji hi).trans
      (congrArg (fun p => -a + (nc k).inv p) heq.symm)
  have hatoms := NormalBallChart.eventually_recenter_apply_eq_of_configuration_convergence
    nc a hr hball hcfg hK hKU (continuous_id.sub continuous_const).continuousOn hcenter
    atom htarget hcoords
  filter_upwards [hatoms, hcoords] with k hk hck z hz i hi
  have h := hk z hz i hi
  have hcoord := hck z hz i hi
  let : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  refine ⟨?_, ?_⟩
  · have hm := ((nc k).recenter a hr (hball k)).restrictBall.map_target h.2.2
    change ((nc k).recenter a hr (hball k)).inv (atom k z i) ∈ Metric.ball (0 : E) r at hm
    rw [h.2.1] at hm
    exact hm
  · exact h.1.trans (dif_pos z.property)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
