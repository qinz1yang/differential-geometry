import DifferentialGeometry.Topology.Manifold.NearestPointStationarity
import Mathlib.Topology.Homeomorph.Lemmas

/-! Exact residual-coordinate images and uniform quarter-core buffers for the same nearest map. -/

set_option autoImplicit false
noncomputable section
open Set Metric Topology
open scoped ContDiff Manifold
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H]

def nearestResidualCoordinates (Ω : TopologicalSpace.Opens H) (Z : Set H) (p : Ω → Z) :
    Ω → Z × H := fun z => (p z, (z : H) - (p z : H))

def nearestDiscDomain (Ω : TopologicalSpace.Opens H) (Z : Set H) (p : Ω → Z)
    (V : Set Z) (ρ : ℝ) : Set Ω := {z | p z ∈ V ∧ ‖(z : H) - (p z : H)‖ ≤ ρ}

def actualNormalDisc [InnerProductSpace ℝ H] (k : ℕ) (Z : Set H)
    [ChartedSpace (Fin k → ℝ) Z] (V : Set Z) (ρ : ℝ) : Set (Z × H) :=
  {yn | yn.1 ∈ V ∧ yn.2 ∈ (actualZeroSetTangentSpace k Z yn.1)ᗮ ∧ ‖yn.2‖ ≤ ρ}

theorem nearestResidualCoordinates_reconstruct (Ω : TopologicalSpace.Opens H) (Z : Set H)
    (p : Ω → Z) (z : Ω) :
    ((nearestResidualCoordinates Ω Z p z).1 : H) +
      (nearestResidualCoordinates Ω Z p z).2 = (z : H) := by
  dsimp only [nearestResidualCoordinates]
  abel

theorem nearestResidualCoordinates_injective (Ω : TopologicalSpace.Opens H) (Z : Set H)
    (p : Ω → Z) : Function.Injective (nearestResidualCoordinates Ω Z p) := by
  intro z w hzw
  apply Subtype.ext
  rw [← nearestResidualCoordinates_reconstruct Ω Z p z,
    ← nearestResidualCoordinates_reconstruct Ω Z p w, hzw]

theorem nearestResidualCoordinates_continuous (Ω : TopologicalSpace.Opens H) (Z : Set H)
    (p : Ω → Z) (hp : Continuous p) : Continuous (nearestResidualCoordinates Ω Z p) :=
  hp.prodMk (continuous_subtype_val.sub (continuous_subtype_val.comp hp))

theorem nearestResidualCoordinates_isEmbedding (Ω : TopologicalSpace.Opens H) (Z : Set H)
    (p : Ω → Z) (hp : Continuous p) : IsEmbedding (nearestResidualCoordinates Ω Z p) := by
  let recover : Z × H → H := fun yn => (yn.1 : H) + yn.2
  have hr : Continuous recover :=
    (continuous_subtype_val.comp continuous_fst).add continuous_snd
  have heq : recover ∘ nearestResidualCoordinates Ω Z p = (Subtype.val : Ω → H) :=
    funext (nearestResidualCoordinates_reconstruct Ω Z p)
  apply IsEmbedding.of_comp (nearestResidualCoordinates_continuous Ω Z p hp) hr
  rw [heq]
  exact IsEmbedding.subtypeVal

def nearestDiscCoordinatesHomeomorph (Ω : TopologicalSpace.Opens H) (Z : Set H)
    (p : Ω → Z) (hp : Continuous p) (V : Set Z) (ρ : ℝ) :
    nearestDiscDomain Ω Z p V ρ ≃ₜ
      (nearestResidualCoordinates Ω Z p '' nearestDiscDomain Ω Z p V ρ) :=
  (nearestResidualCoordinates_isEmbedding Ω Z p hp).homeomorphImage
    (nearestDiscDomain Ω Z p V ρ)

theorem mem_nearestDiscCoordinatesImage_iff {Ω : TopologicalSpace.Opens H} {Z : Set H}
    {p : Ω → Z} {V : Set Z} {ρ : ℝ} {yn : Z × H} :
    yn ∈ nearestResidualCoordinates Ω Z p '' nearestDiscDomain Ω Z p V ρ ↔
      yn.1 ∈ V ∧ ‖yn.2‖ ≤ ρ ∧
        ∃ hz : (yn.1 : H) + yn.2 ∈ Ω, p ⟨(yn.1 : H) + yn.2, hz⟩ = yn.1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨hz.1, hz.2, ?_⟩
    have heq := nearestResidualCoordinates_reconstruct Ω Z p z
    refine ⟨heq.symm ▸ z.property, ?_⟩
    congr 1
    exact Subtype.ext heq
  · rintro ⟨hy, hn, hz, hp⟩
    let z : Ω := ⟨(yn.1 : H) + yn.2, hz⟩
    have hcoord : nearestResidualCoordinates Ω Z p z = yn := by
      apply Prod.ext
      · exact hp
      · change (yn.1 : H) + yn.2 - (p z : H) = yn.2
        rw [hp]
        abel
    refine ⟨z, ?_, hcoord⟩
    change p z ∈ V ∧ ‖(z : H) - (p z : H)‖ ≤ ρ
    rw [hp]
    exact ⟨hy, by simpa only [z, add_sub_cancel_left] using hn⟩

theorem nearestDiscCoordinatesImage_subset_normalDisc [InnerProductSpace ℝ H]
    {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
    (Ω : TopologicalSpace.Opens H)
    (p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯)
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H))
    (hnearest : ∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H))
    (V : Set Z) (ρ : ℝ) :
    nearestResidualCoordinates Ω Z p '' nearestDiscDomain Ω Z p V ρ ⊆
      actualNormalDisc k Z V ρ := by
  rintro yn ⟨z, hz, rfl⟩
  exact ⟨hz.1, nearestMap_residual_mem_actual_normal Ω p hemb hnearest z, hz.2⟩

def originalNearestCore (S : Set H) (r : H → ℝ) : TopologicalSpace.Opens H :=
  ⟨⋃ x : S, ball (x : H) (r x), isOpen_iUnion (fun x => isOpen_ball (x := (x : H)) (ε := r x))⟩

def nearestQuarterBase (S : Set H) (r : H → ℝ) (Z : Set H) : TopologicalSpace.Opens Z :=
  ⟨{y | (y : H) ∈ ⋃ x : S, ball (x : H) (r x / 4)},
    (isOpen_iUnion (fun x : S =>
      isOpen_ball (x := (x : H)) (ε := r x / 4))).preimage continuous_subtype_val⟩

theorem mem_originalNearestCore_of_quarterBase (S : Set H) (r : H → ℝ) (Z : Set H)
    (rmin : ℝ) (hrmin : 0 < rmin) (hlower : ∀ x ∈ S, rmin ≤ r x)
    (y : Z) (hy : y ∈ nearestQuarterBase S r Z) (n : H) (hn : ‖n‖ ≤ rmin / 4) :
    (y : H) + n ∈ originalNearestCore S r := by
  obtain ⟨x, hx⟩ := mem_iUnion.mp hy
  apply mem_iUnion.mpr
  refine ⟨x, ?_⟩
  have hdist : ‖(y : H) - x‖ < r x / 4 := by
    simpa only [mem_ball, dist_eq_norm] using hx
  have hl := hlower x x.property
  have heq : (y : H) + n - x = ((y : H) - x) + n := by abel
  rw [mem_ball, dist_eq_norm, heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

end GC.MetricGeometry
