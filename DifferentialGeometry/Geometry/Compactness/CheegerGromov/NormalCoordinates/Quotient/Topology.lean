import DifferentialGeometry.Topology.Attachment.TransitionGluing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.LimitDomains
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.LimitIdentities
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.CenterClassification

section

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

def IntrinsicBallChart.bufferedTransitionGlueData
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
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a)) :
    TopCat.GlueData.{uE} := by
  have hrefl : ∀ i, near i i = true := by
    intro i
    apply EMetric.eq_true_self_of_eventually_edist_lt_or_ge x (l := atTop)
      (by positivity : 0 < ENNReal.ofReal (ρ / 4)) near hclass i
  have hsymm : ∀ i j, near i j = true → near j i = true := by
    intro i j hij
    have hs := EMetric.eq_swap_of_eventually_edist_lt_or_ge x (l := atTop) near hclass i j
    rw [← hs]
    exact hij
  let U : Set E := Metric.ball (0 : E) (ρ / 8)
  have hU : IsOpen U := Metric.isOpen_ball
  have hsub : U ⊆ Metric.ball (0 : E) (ρ / 2) := Metric.ball_subset_ball (by linarith)
  have hself : ∀ i z, z ∈ U → J ⟨(i,i),hrefl i⟩ z = z := by
    intro i z hz
    have heq := NormalBallChart.transition_limit_self
      (fun k => (c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ)
      (hconv ⟨(i,i),hrefl i⟩) (fun z hz => Filter.Eventually.of_forall (fun k => by
        change z ∈ (c i k).hom.source
        rw [(c i k).source_eq]
        exact Metric.ball_subset_ball (by linarith) hz))
    exact heq (hsub hz)
  have hinv : ∀ i j (h : near i j = true) z, z ∈ U → J ⟨(i,j),h⟩ z ∈ U →
      J ⟨(j,i),hsymm i j h⟩ (J ⟨(i,j),h⟩ z) = z := by
    intro i j hij z hz _
    have hnear : ∀ᶠ k in atTop, edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4) :=
      (hclass i j).mono fun k hk => hk.1 hij
    have hi := IntrinsicBallChart.transition_limit_inverse_on_ball_of_lt g hEnorm (x i) (x j) hρ
      (c i) (c j) (s := ρ / 8) (by positivity) (by linarith) (hconv ⟨(i,j),hij⟩) (hconv ⟨(j,i),hsymm i j hij⟩)
      (hcont ⟨(i,j),hij⟩) (hcont ⟨(j,i),hsymm i j hij⟩) hnear
    exact hi.1 hz
  have htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) z,
      z ∈ U → J ⟨(i,j),hij⟩ z ∈ U → J ⟨(j,k),hjk⟩ (J ⟨(i,j),hij⟩ z) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i,k),hik⟩ z = J ⟨(j,k),hjk⟩ (J ⟨(i,j),hij⟩ z) := by
    intro i j k hij hjk z hz h1 h2
    exact IntrinsicBallChart.transition_limit_trans_on_ball g hEnorm x hρ c near hclass J hcont hconv (s := ρ / 8) (by positivity) le_rfl hij hjk hz h1 h2
  exact TopCat.GlueData.ofTransitionMaps (U := U) (hU := hU) (near := near) (J := J)
    (hJ := fun a => (hcont a).mono hsub) (hrefl := hrefl) (hsymm := hsymm)
    (hself := hself) (hinv := hinv) (htrans := htrans)
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

theorem IntrinsicBallChart.bufferedTransitionGlueData_index :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J = ι := rfl

theorem IntrinsicBallChart.bufferedTransitionGlueData_patch (i : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).U i =
      TopCat.of (Metric.ball (0 : E) (ρ / 8)) := rfl

theorem IntrinsicBallChart.bufferedTransitionGlueData_overlap (i j : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).V (i,j) =
      TopCat.of {z : Metric.ball (0 : E) (ρ / 8) |
        ∃ h : near i j = true, J ⟨(i,j),h⟩ z ∈ Metric.ball (0 : E) (ρ / 8)} := rfl

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

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
    {N : ℕ} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : (Fin (N + 1)) → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : (Fin (N + 1)) → (Fin (N + 1)) → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : (Fin (N + 1)) × (Fin (N + 1)) // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


def IntrinsicBallChart.finiteBufferedTransitionGlueData : TopCat.GlueData.{uE} :=
  IntrinsicBallChart.bufferedTransitionGlueData g hEnorm
    (fun i : ULift.{uE} (Fin (N + 1)) => x i.down) hρ
    (fun i k => c i.down k) (fun i j => near i.down j.down)
    (fun i j => hclass i.down j.down)
    (fun a => J ⟨(a.1.1.down, a.1.2.down), a.2⟩)
    (fun a => hcont ⟨(a.1.1.down, a.1.2.down), a.2⟩)
    (fun a => hconv ⟨(a.1.1.down, a.1.2.down), a.2⟩)

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_index :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J =
      ULift.{uE} (Fin (N + 1)) := rfl

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_patch (i : ULift.{uE} (Fin (N + 1))) :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).U i =
      TopCat.of (Metric.ball (0 : E) (ρ / 8)) := rfl

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap (i j : ULift.{uE} (Fin (N + 1))) :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).V (i,j) =
      TopCat.of {z : Metric.ball (0 : E) (ρ / 8) |
        ∃ h : near i.down j.down = true,
          J ⟨(i.down,j.down),h⟩ z ∈ Metric.ball (0 : E) (ρ / 8)} := rfl

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

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

theorem IntrinsicBallChart.bufferedTransitionGlueData_t2Space :
    T2Space (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData
  exact TopCat.GlueData.t2Space_ofTransitionMaps _ _ _ _ _ _ _ _ _ _

def IntrinsicBallChart.transitionGlueCore :
    Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  ⋃ i, (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i ''
    {z : Metric.ball (0 : E) (ρ / 8) | (z : E) ∈ Metric.ball 0 (ρ / 10)}

def IntrinsicBallChart.transitionGlueCompactCore :
    Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  ⋃ i, Set.range (fun z : Metric.closedBall (0 : E) (ρ / 10) =>
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i
      ⟨z, lt_of_le_of_lt z.property (by linarith : ρ / 10 < ρ / 8)⟩)

theorem IntrinsicBallChart.isOpen_transitionGlueCore :
    IsOpen (IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv) := by
  apply isOpen_iUnion
  intro i
  apply (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).ι_isOpenEmbedding i |>.isOpenMap
  exact Metric.isOpen_ball.preimage continuous_subtype_val

theorem IntrinsicBallChart.zero_mem_transitionGlueCore (i : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i
      ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈
      IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv := by
  exact mem_iUnion.mpr ⟨i, ⟨⟨0, Metric.mem_ball_self (by positivity)⟩,
    Metric.mem_ball_self (by positivity), rfl⟩⟩

theorem IntrinsicBallChart.isCompact_transitionGlueCompactCore [Finite ι] :
    IsCompact (IntrinsicBallChart.transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv) := by
  let : Finite (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J := by
    change Finite ι
    infer_instance
  apply isCompact_iUnion
  intro i
  apply isCompact_range
  apply ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i).hom.continuous.comp
  exact continuous_subtype_val.subtype_mk _

theorem IntrinsicBallChart.transitionGlueCore_subset_compactCore :
    IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv ⊆
      IntrinsicBallChart.transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv := by
  rintro z ⟨_, ⟨i, rfl⟩, ⟨w, hw, rfl⟩⟩
  exact mem_iUnion.mpr ⟨i, ⟨⟨(w : Metric.ball (0 : E) (ρ / 8)).val, Metric.ball_subset_closedBall hw⟩, rfl⟩⟩

theorem IntrinsicBallChart.isCompact_closure_transitionGlueCore [Finite ι] :
    IsCompact (closure (IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv)) := by
  let : T2Space (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space _ _ _ _ _ _ _ _ _ _
  have hK := IntrinsicBallChart.isCompact_transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (IntrinsicBallChart.transitionGlueCore_subset_compactCore g hEnorm x hρ c near hclass J hcont hconv) hK.isClosed)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

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
    {N : ℕ} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : (Fin (N + 1)) → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : (Fin (N + 1)) → (Fin (N + 1)) → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : (Fin (N + 1)) × (Fin (N + 1)) // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space :
    T2Space (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  unfold IntrinsicBallChart.finiteBufferedTransitionGlueData
  exact IntrinsicBallChart.bufferedTransitionGlueData_t2Space _ _ _ _ _ _ _ _ _ _

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology :
    SecondCountableTopology (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  let D := IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
  let : Countable D.J := by
    change Countable (ULift.{uE} (Fin (N + 1)))
    infer_instance
  let : ∀ i : D.J, SecondCountableTopology (D.U i) := by
    intro i
    change SecondCountableTopology (Metric.ball (0 : E) (ρ / 8))
    infer_instance
  exact TopCat.GlueData.secondCountableTopology D

def IntrinsicBallChart.bufferedTransitionGlueBasepoint :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι
    (ULift.up 0) ⟨0, Metric.mem_ball_self (by positivity)⟩

theorem IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range :
    IntrinsicBallChart.bufferedTransitionGlueBasepoint g hEnorm x hρ c near hclass J hcont hconv ∈
      Set.range ((IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι (ULift.up 0)) :=
  ⟨⟨0, Metric.mem_ball_self (by positivity)⟩, rfl⟩

include hρ in
theorem IntrinsicBallChart.pointed_intrinsic_chart_zero
    (p : ∀ k, M k) (hbase : ∀ k, x 0 k = p k) (k : ℕ) :
    (c 0 k).hom 0 = p k := by
  calc
    (c 0 k).hom 0 = x 0 k := ((c 0 k).toNormalBallChart (g k) (hEnorm k) (x 0 k) hρ).map_zero
    _ = p k := hbase k

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
