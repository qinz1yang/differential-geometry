import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTorusBicollar
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Taming

set_option autoImplicit false

/-!
# Polyhedral bicollar model for finitely many tori (LT-P2)

Finitely many translated, shrunk copies of the polyhedral donut bicollar, glued into one open
partial homeomorphism `(ι × Torus) × ℝ → ℝ³` with source `-1 < s < 1` and polyhedral zero level.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A polyhedral donut bicollar whose image on the whole source is bounded. -/
theorem exists_bounded_polyhedral_bicollar_LTP2 :
    ∃ Φ : OpenPartialHomeomorph (Torus × ℝ) ℝ³,
      Φ.source = {p | -1 < p.2 ∧ p.2 < 1} ∧ IsPolyhedron (range fun t => Φ (t, 0)) ∧
        ∃ R : ℝ, ∀ p ∈ Φ.source, ‖Φ p‖ < R := by
  obtain ⟨Φ0, hΦ0, hQ⟩ := exists_polyhedral_bicollar_model
  obtain ⟨R0, hR0⟩ := hQ.isCompact.isBounded.subset_ball (0 : ℝ³)
  have h0 : ∀ t : Torus, (t, (0 : ℝ)) ∈ Φ0.source := fun t => by
    rw [hΦ0]; exact ⟨by norm_num, by norm_num⟩
  let n : Set (Torus × ℝ) := Φ0.source ∩ Φ0 ⁻¹' Metric.ball 0 R0
  have hn : IsOpen n := Φ0.continuousOn.isOpen_inter_preimage Φ0.open_source Metric.isOpen_ball
  have hsub : (univ : Set Torus) ×ˢ ({0} : Set ℝ) ⊆ n := by
    rintro ⟨t, s⟩ ⟨-, hs⟩
    have : s = 0 := hs
    subst this
    exact ⟨h0 t, hR0 ⟨t, rfl⟩⟩
  obtain ⟨u, v, -, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hn hsub
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  set δ : ℝ := min ε 1 with hδ
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hδn : ∀ (t : Torus) (s : ℝ), |s| < 1 → (t, δ * s) ∈ n := by
    intro t s hs
    refine huv ⟨hu (mem_univ t), hεv ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul, abs_of_pos hδ0]
    nlinarith
  let e : OpenPartialHomeomorph (Torus × ℝ) (Torus × ℝ) :=
    (Homeomorph.prodCongr (Homeomorph.refl Torus) (Homeomorph.mulLeft₀ δ hδ0.ne')).toOpenPartialHomeomorph
  let S : Set (Torus × ℝ) := {p | -1 < p.2 ∧ p.2 < 1}
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  let Φ : OpenPartialHomeomorph (Torus × ℝ) ℝ³ := (e.trans Φ0).restrOpen S hS
  have hΦ : ∀ p, Φ p = Φ0 (p.1, δ * p.2) := fun p => rfl
  have hsrc : Φ.source = S := by
    ext p
    change (p ∈ e.source ∧ e p ∈ Φ0.source) ∧ p ∈ S ↔ p ∈ S
    constructor
    · exact fun h => h.2
    · intro hp
      have hp' : |p.2| < 1 := abs_lt.mpr hp
      exact ⟨⟨trivial, (hδn p.1 p.2 hp').1⟩, hp⟩
  refine ⟨Φ, hsrc, ?_, R0, ?_⟩
  · convert hQ using 2
    ext t
    simp [hΦ]
  · intro p hp
    rw [hsrc] at hp
    have := (hδn p.1 p.2 (abs_lt.mpr hp)).2
    simpa [hΦ] using this

variable {ι : Type} [Finite ι] [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι]

theorem exists_polyhedral_bicollar_model_family_LTP2 :
    ∃ Φ : OpenPartialHomeomorph ((ι × Torus) × ℝ) ℝ³,
      Φ.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
        IsPolyhedron (range fun x : ι × Torus => Φ (x, 0)) := by
  obtain ⟨Φ1, hΦ1, hQ, R0, hR0⟩ := exists_bounded_polyhedral_bicollar_LTP2
  set R : ℝ := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRb : ∀ p ∈ Φ1.source, ‖Φ1 p‖ < R := fun p hp => (hR0 p hp).trans_le (le_max_left _ _)
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let o : ι → ℝ³ := fun i => (4 * R * ((e i : ℕ) : ℝ)) • EuclideanSpace.single 0 (1 : ℝ)
  have ho : ∀ i j, i ≠ j → 2 * R < ‖o i - o j‖ := by
    intro i j hij
    have hne : (e i : ℕ) ≠ (e j : ℕ) := fun h => hij (e.injective (Fin.ext h))
    have : o i - o j = (4 * R * (((e i : ℕ) : ℝ) - ((e j : ℕ) : ℝ))) • EuclideanSpace.single 0 (1 : ℝ) := by
      simp only [o, ← sub_smul]; congr 1; ring
    rw [this, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_mul, abs_of_pos (by linarith : 0 < 4 * R)]
    have h1 : (1 : ℝ) ≤ |((e i : ℕ) : ℝ) - ((e j : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_sub_comm]
        have : (((e i : ℕ) : ℝ)) + 1 ≤ ((e j : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (((e j : ℕ) : ℝ)) + 1 ≤ ((e i : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith
  let S : Set ((ι × Torus) × ℝ) := {p | -1 < p.2 ∧ p.2 < 1}
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  let F : (ι × Torus) × ℝ → ℝ³ := fun p => o p.1.1 + Φ1 (p.1.2, p.2)
  have hFc : ContinuousOn F S := by
    have hm : Continuous fun p : (ι × Torus) × ℝ => (p.1.2, p.2) := by fun_prop
    have h1 : ContinuousOn (fun p : (ι × Torus) × ℝ => Φ1 (p.1.2, p.2)) S :=
      Φ1.continuousOn.comp hm.continuousOn (fun p hp => by rw [hΦ1]; exact hp)
    have h2 : Continuous fun p : (ι × Torus) × ℝ => o p.1.1 :=
      (continuous_of_discreteTopology (f := o)).comp (continuous_fst.comp continuous_fst)
    exact h2.continuousOn.add h1
  have hFi : InjOn F S := by
    rintro ⟨⟨i, t⟩, s⟩ hp ⟨⟨j, t'⟩, s'⟩ hq h
    have hp' : (t, s) ∈ Φ1.source := by rw [hΦ1]; exact hp
    have hq' : (t', s') ∈ Φ1.source := by rw [hΦ1]; exact hq
    change o i + Φ1 (t, s) = o j + Φ1 (t', s') at h
    by_cases hij : i = j
    · subst hij
      have := Φ1.injOn hp' hq' (add_left_cancel h)
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · exfalso
      have h2 := ho i j hij
      have : o i - o j = Φ1 (t', s') - Φ1 (t, s) := by
        rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
      rw [this] at h2
      have := (norm_sub_le _ _).trans_lt (add_lt_add (hRb _ hq') (hRb _ hp'))
      linarith
  have hFo : ∀ V, V ⊆ S → IsOpen V → IsOpen (F '' V) := by
    intro V hVS hV
    have : F '' V = ⋃ j : ι, (fun y => o j + y) '' (Φ1 '' ((fun q : Torus × ℝ => ((j, q.1), q.2)) ⁻¹' V)) := by
      ext y
      simp only [mem_image, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨⟨j, t⟩, s⟩, hp, rfl⟩
        exact ⟨j, _, ⟨(t, s), hp, rfl⟩, rfl⟩
      · rintro ⟨j, _, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨_, hq, rfl⟩
    rw [this]
    refine isOpen_iUnion fun j => ?_
    have hemb : Continuous fun q : Torus × ℝ => ((j, q.1), q.2) := by fun_prop
    have hsub : ((fun q : Torus × ℝ => ((j, q.1), q.2)) ⁻¹' V) ⊆ Φ1.source := by
      intro q hq; rw [hΦ1]; exact hVS hq
    exact (Homeomorph.addLeft (o j)).isOpenMap _
      (Φ1.isOpen_image_of_subset_source (hV.preimage hemb) hsub)
  haveI : Nonempty ((ι × Torus) × ℝ) := ⟨((Classical.arbitrary ι, (1, 1)), 0)⟩
  let Φ : OpenPartialHomeomorph ((ι × Torus) × ℝ) ℝ³ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hFi.toPartialEquiv F S) hFc
      (by
        intro V hV
        have h1 : IsOpen (Subtype.val '' V : Set _) := hS.isOpenMap_subtype_val V hV
        have h2 := hFo _ (by rintro _ ⟨v, _, rfl⟩; exact v.2) h1
        have : (S.domRestrict F) '' V = F '' (Subtype.val '' V) := by
          rw [← image_comp]; rfl
        change IsOpen ((S.domRestrict F) '' V)
        rwa [this])
      hS
  refine ⟨Φ, rfl, ?_⟩
  have : (range fun x : ι × Torus => Φ (x, 0)) =
      ⋃ j : ι, (fun y => o j + y) '' (range fun t : Torus => Φ1 (t, 0)) := by
    ext y
    simp only [mem_range, mem_iUnion, mem_image]
    constructor
    · rintro ⟨⟨j, t⟩, rfl⟩
      exact ⟨j, _, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨j, _, ⟨t, rfl⟩, rfl⟩
      exact ⟨(j, t), rfl⟩
  rw [this]
  exact IsPolyhedron.iUnion fun j => by
    have := hQ.image_affineEquiv (AffineEquiv.constVAdd ℝ ℝ³ (o j))
    convert this using 1; rfl

end GC.LongTime.CuspP1
