/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem isEmbedding_domRestrict_of_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {K U : Set X}
    (hf : Topology.IsEmbedding (K.domRestrict f)) (hUK : U ⊆ K) :
    Topology.IsEmbedding (U.domRestrict f) :=
  hf.comp (Topology.IsEmbedding.inclusion hUK)

private theorem isPLOn_id_of_isOpen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {s : Set M}
    (hs : IsOpen s) : IsPLOn n n (id : M → M) s := by
  intro x hx
  have hnb : s ∈ 𝓝[(univ : Set M)] x := by
    rw [nhdsWithin_univ]
    exact hs.mem_nhds hx
  have h₂ : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) (id : M → M)
      (univ ∩ s) x :=
    (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mpr (isPL_id x)
  rwa [univ_inter] at h₂

theorem exists_isSubdivision_diam_image_closedStars_lt {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace Z] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {g : E → Z} (hg : ContinuousOn g K.space) {φ : E → ℝ} (hφ : ContinuousOn φ K.space)
    (hpos : ∀ x ∈ K.space, 0 < φ x) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∀ x ∈ ⋃ v ∈ s, closedStar R v,
        Metric.diam (g '' ⋃ v ∈ s, closedStar R v) < φ x := by
  have hKc : IsCompact K.space :=
    DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K
  obtain ⟨c, hc, hcle⟩ := exists_pos_forall_le_of_continuousOn hKc hφ hpos
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hg) (c / 2) (by positivity)
  obtain ⟨R, hR, hRfin, hstar⟩ :=
    exists_isSubdivision_closedStars_subset_cover K
      (fun z : K.space => Metric.ball (z : E) (δ / 2))
      (fun _ => Metric.isOpen_ball.preimage continuous_subtype_val)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (half_pos hδ)⟩)
  refine ⟨R, hR, hRfin, fun s hs x hx => ?_⟩
  obtain ⟨z, hz⟩ := hstar s hs
  have hsub : (⋃ v ∈ s, closedStar R v) ⊆ K.space :=
    iUnion₂_subset fun v _ => (closedStar_subset_space R v).trans hR.space_eq.subset
  have hdiam : Metric.diam (g '' ⋃ v ∈ s, closedStar R v) ≤ c / 2 := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    refine le_of_lt (hclose y (hsub hy) y' (hsub hy') ?_)
    have h₁ : dist y (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy)
    have h₂ : dist y' (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy')
    calc dist y y' ≤ dist y (z : E) + dist (z : E) y' := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (z : E) y']; linarith
  exact hdiam.trans_lt (lt_of_lt_of_le (by linarith) (hcle x (hsub hx)))

def Moise352InwardPush (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x

theorem exists_isPLOn_injOn_leftInvOn_of_isOpen {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    {K : Set M₁} (hK : IsOpen K) (h : M₁ → M₂) {ψ : M₁ → ℝ}
    (hψ : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x :=
  ⟨id, id, K, hK, hK.interior_eq.ge, mapsTo_id K, isPLOn_id_of_isOpen hK, injOn_id K,
    isPLOn_id_of_isOpen hK, mapsTo_id K, fun _ _ => rfl, fun x hx => by simpa using hψ x hx⟩

def Moise352SkeletonExtension (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ φ : M₁ → ℝ, ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    (∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
      ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
        IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
        ∀ x ∈ K, dist (h (p x)) (h x) < ψ x) →
    (∀ {U : Set M₁}, IsOpen U → U ⊆ K → ∀ {G : Set M₁}, G ⊆ U →
      IsClosed (((↑) : U → M₁) ⁻¹' G) → IsLocallyFinitePolyhedralGraph (n := n) G →
      ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
        ∃ N : Set M₁, IsLocallyFiniteRegularNeighborhoodOf (n := n) N G U ∧
          ∃ f : M₁ → M₂, IsPLHomeomorphInto n f N ∧ f '' N ∈ nhdsSet (h '' G) ∧
            ∀ x ∈ N, dist (f x) (h x) < ψ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x

theorem moise352_of_inwardPush_of_skeletonExtension (hpush : Moise352InwardPush.{u} 3)
    (h351 : Moise351.{u}) (hext : Moise352SkeletonExtension.{u} 3) : Moise352.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  refine hext hK hh φ hφ hpos (fun ψ hψ hψpos => hpush hK hh ψ hψ hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

theorem exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen (h351 : Moise351.{u})
    (hext : Moise352SkeletonExtension.{u} 3) {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [Nonempty M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {K : Set M₁}
    (hK : IsOpen K) {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (φ : M₁ → ℝ)
    (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x := by
  refine hext (isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) hK) hh φ hφ hpos
    (fun _ _ hψpos => exists_isPLOn_injOn_leftInvOn_of_isOpen hK h hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

theorem exists_isPLHomeomorphInto_dist_lt_id_of_isOpen {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Set M}
    (hK : IsOpen K) {φ : M → ℝ} (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M → M, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (id x) < φ x := by
  refine ⟨id, ⟨isPLOn_id_of_isOpen hK, injOn_id K, ?_⟩, fun x hx => by simpa using hpos x hx⟩
  intro y hy
  rw [Set.image_id] at hy
  exact ⟨id, by rw [Set.image_id]; exact isPLOn_id_of_isOpen hK y hy, fun _ _ => rfl⟩

theorem isLocallyFinitePolyhedralManifoldWithBoundary_univ_three :
    (univ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty ∧
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3
        (univ : Set (EuclideanSpace ℝ (Fin 3))) ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphInto 3 f univ ∧
          ∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))), dist (f x) (id x) < 1 :=
  ⟨univ_nonempty, isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) isOpen_univ,
    exists_isPLHomeomorphInto_dist_lt_id_of_isOpen isOpen_univ fun _ _ => one_pos⟩

end DifferentialGeometry.Topology.PiecewiseLinear
