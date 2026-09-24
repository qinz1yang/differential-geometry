/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import Mathlib.Analysis.Normed.Module.Connected

/-! # Section34Piercing Nonempty -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Annulus

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {A A₀ A₁ : Set X}

theorem IsAnnulusOn.isConnected (hann : IsAnnulusOn A A₀ A₁) : IsConnected A := by
  obtain ⟨φ, -, -⟩ := hann
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    apply isConnected_sphere _ _ zero_le_one
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Subtype.connectedSpace hs
  let : ConnectedSpace (Icc (0 : ℝ) 1) := Subtype.connectedSpace (isConnected_Icc zero_le_one)
  have hrange : range (fun p => ((φ p : A) : X)) = A := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (φ p).property
    · intro hx
      obtain ⟨p, hp⟩ := φ.surjective ⟨x, hx⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  rw [← hrange]
  exact isConnected_range (continuous_subtype_val.comp φ.continuous)

theorem IsAnnulusOn.boundaries_nonempty (hann : IsAnnulusOn A A₀ A₁) :
    A₀.Nonempty ∧ A₁.Nonempty := by
  obtain ⟨φ, h₀, h₁⟩ := hann
  obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty
    (E := EuclideanSpace ℝ (Fin 2)) (x := 0) (r := 1) |>.mpr zero_le_one
  rw [h₀, h₁]
  simp only [image_nonempty]
  exact ⟨⟨(⟨p, hp⟩, ⟨0, by norm_num⟩), rfl⟩,
    ⟨(⟨p, hp⟩, ⟨1, by norm_num⟩), rfl⟩⟩

theorem IsAnnulusOn.image_inter_frontier_nonempty (hann : IsAnnulusOn A A₀ A₁)
    {f : X → Y} (hf : ContinuousOn f A) {C : Set Y}
    (hinside : f '' A₀ ⊆ interior C) (houtside : Disjoint (f '' A₁) C) :
    (f '' A ∩ frontier C).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := hann.boundaries_nonempty.1
  obtain ⟨x₁, hx₁⟩ := hann.boundaries_nonempty.2
  have hconn := hann.isConnected.isPreconnected.image f hf
  by_contra hne
  have havoid : Disjoint (f '' A) (frontier C) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
  have hcover : f '' A ⊆ interior C ∪ (closure C)ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure C
    · refine Or.inl ?_
      by_contra hyn
      exact Set.disjoint_left.mp havoid hy ⟨hyc, hyn⟩
    · exact Or.inr hyc
  have hsub : f '' A ⊆ interior C := hconn.subset_left_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun y hy hyc => hyc (interior_subset_closure hy))
    hcover ⟨f x₀, mem_image_of_mem f (hann.first_subset hx₀),
      hinside (mem_image_of_mem f hx₀)⟩
  exact Set.disjoint_left.mp houtside (mem_image_of_mem f hx₁)
    (interior_subset (hsub (mem_image_of_mem f (hann.second_subset hx₁))))

end Annulus

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_piercing_trace_nonempty
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore
      Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w)
    (hinside : ∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2)) :
    ∀ e, (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e).Nonempty := by
  obtain ⟨-, -, -, -, hcp, -, -, -, -, -, -, -, -, -, haa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, hcross, hout, -⟩ := section34MarginConditions hprep hGdist
  intro e
  have hAa : Aa e ⊆ CpBd (ends e).1 := by
    rw [(haa e).1]
    exact inter_subset_left
  have hAaCp : Aa e ⊆ Cp (ends e).1 := hAa.trans (hcp (ends e).1).boundary_subset
  obtain ⟨y, hyA, hyBd⟩ := (haa e).2.image_inter_frontier_nonempty
    ((hGp (ends e).1).continuousOn.mono hAaCp) (hinside e) (hout e)
  rw [← ((hcp (ends e).2).image_boundary_interior (hGp (ends e).2)).1] at hyBd
  have hyCross := hcross e ⟨(image_mono hAa) hyA, hyBd⟩
  exact ⟨y, hyA, (image_mono sdiff_subset) hyCross.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
