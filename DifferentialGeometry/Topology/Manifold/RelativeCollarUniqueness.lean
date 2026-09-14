import DifferentialGeometry.Topology.Manifold.RelativeCollar
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

open Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Collar

universe u

private theorem norm_fin_one_eq_abs (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

private theorem exists_pos_forall_mem_of_mem_nhds_zero
    {V : Set (EuclideanHalfSpace 1)} (hV : V ∈ 𝓝 (0 : EuclideanHalfSpace 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : EuclideanHalfSpace 1, t.1 0 < ε → t ∈ V := by
  obtain ⟨u, hu, huV⟩ := (mem_nhds_subtype {x : EuclideanSpace ℝ (Fin 1) | 0 ≤ x 0}
    (0 : EuclideanHalfSpace 1) V).mp hV
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r, hr, fun t ht => huV ?_⟩
  refine hrsub ?_
  rw [Metric.mem_ball]
  have hmem : dist t.1 (0 : EuclideanSpace ℝ (Fin 1)) < r := by
    rw [dist_eq_norm, sub_zero, norm_fin_one_eq_abs, abs_of_nonneg t.2]
    exact ht
  exact hmem

theorem exists_pos_forall_mem_of_isCompact_zeroSection
    {S : Type*} [TopologicalSpace S] {K : Set S} (hK : IsCompact K)
    {W : Set (S × EuclideanHalfSpace 1)} (hW : IsOpen W)
    (h0 : ∀ p ∈ K, (p, 0) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ K, ∀ t : EuclideanHalfSpace 1, t.1 0 < δ → (p, t) ∈ W := by
  have hbox : ∀ p : K, ∃ U : Set S, ∃ V : Set (EuclideanHalfSpace 1),
      IsOpen U ∧ IsOpen V ∧ (p : S) ∈ U ∧ (0 : EuclideanHalfSpace 1) ∈ V ∧
        U ×ˢ V ⊆ W :=
    fun p => isOpen_prod_iff.mp hW p.1 0 (h0 p.1 p.2)
  choose U V hUopen hVopen hUp hV0 hUV using hbox
  have hε : ∀ p : K, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : EuclideanHalfSpace 1, t.1 0 < ε → t ∈ V p :=
    fun p => exists_pos_forall_mem_of_mem_nhds_zero ((hVopen p).mem_nhds (hV0 p))
  choose ε hεpos hεV using hε
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U (fun p => hUopen p)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hUp ⟨x, hx⟩⟩)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact ⟨1, one_pos, fun p hp => absurd (hT hp) (by simp)⟩
  · refine ⟨T.inf' hTne ε, (Finset.lt_inf'_iff hTne).mpr fun p _ => hεpos p, ?_⟩
    intro p hp t ht
    obtain ⟨i, hiT, hpi⟩ := Set.mem_iUnion₂.mp (hT hp)
    exact hUV i ⟨hpi, hεV i t (lt_of_lt_of_le ht (Finset.inf'_le ε hiT))⟩

theorem exists_pos_forall_mem_of_compact_zeroSection
    {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {W : Set (S × EuclideanHalfSpace 1)} (hW : IsOpen W)
    (h0 : ∀ p : S, (p, 0) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p : S, ∀ t : EuclideanHalfSpace 1, t.1 0 < δ → (p, t) ∈ W := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_pos_forall_mem_of_isCompact_zeroSection (K := univ) isCompact_univ hW
      (fun p _ => h0 p)
  exact ⟨δ, hδ, fun p t ht => h p (mem_univ p) t ht⟩

private theorem eqOn_symm_of_eqOn_id {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    {Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞} {X : Set M}
    (h : Set.EqOn Φ id X) : Set.EqOn Φ.symm id X := by
  intro x hx
  have hx' : Φ x = x := h hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [hx']
    _ = x := Diffeomorph.symm_apply_apply Φ x

def BoundaryCollarRegularization : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
        ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            Φ (c₀ (p, t)) = c₁ (p, t)) ∧
          Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ})ᶜ

theorem relativeBoundaryCollarUniqueness_of_regularization
    (h : BoundaryCollarRegularization.{u}) :
    ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ U : Set M, IsOpen U →
        (∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
          c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            (p, t) ∈ c₀.source ∧ (p, t) ∈ c₁.source ∧
              c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) ∧
          ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
            (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
              Φ (c₀ (p, t)) = c₁ (p, t)) ∧
            Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy U _ ⟨ε, hε, hU⟩
  obtain ⟨δsrc, hδsrc, hstrip⟩ := exists_pos_forall_mem_of_compact_zeroSection
    (S := S) (W := c₀.source ∩ c₁.source)
    (c₀.open_source.inter c₁.open_source) (fun p => ⟨(hsrc p).1, (hsrc p).2⟩)
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ :=
    h c₀ c₁ hsrc hcore hbdy (min δsrc ε) (lt_min hδsrc hε)
  have hδsrc' : δ ≤ δsrc := hδε.trans (min_le_left _ _)
  have hδε' : δ ≤ ε := hδε.trans (min_le_right _ _)
  have hsub : Uᶜ ⊆ (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ})ᶜ := by
    rintro x hx ⟨q, hq, rfl⟩
    exact hx (hU q.1 q.2 (lt_of_lt_of_le hq hδε')).1
  refine ⟨δ, hδ, fun p t ht => ?_, Φ, hmatch, Set.EqOn.mono hsub hsupp,
    eqOn_symm_of_eqOn_id (Set.EqOn.mono hsub hsupp)⟩
  · exact ⟨(hstrip p t (lt_of_lt_of_le ht hδsrc')).1,
      (hstrip p t (lt_of_lt_of_le ht hδsrc')).2,
      (hU p t (lt_of_lt_of_le ht hδε')).1, (hU p t (lt_of_lt_of_le ht hδε')).2⟩

theorem exists_diffeomorph_of_eqOn_halfStrip
    {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hagree : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε → c₀ (p, t) = c₁ (p, t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
        (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
          Φ (c₀ (p, t)) = c₁ (p, t)) ∧
        Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ})ᶜ := by
  refine ⟨ε, hε, le_rfl, Diffeomorph.refl (𝓡∂ 3) M ∞, fun p t ht => hagree p t ht, ?_⟩
  intro x _
  rfl

end DifferentialGeometry.Topology.Collar
