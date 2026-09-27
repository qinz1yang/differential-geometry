import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCirclePair
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_eq_band_of_end_caps {M : Type*} [TopologicalSpace M]
    {S C F D₀ D₁ J₀ J₁ : Set M} (hFS : F ⊆ S) (hFC : F ⊆ C)
    (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S) (hcover : S ⊆ D₀ ∪ D₁ ∪ F)
    (hconn₀ : IsPreconnected (D₀ \ J₀)) (hconn₁ : IsPreconnected (D₁ \ J₁))
    (hF₀ : F ∩ D₀ = J₀) (hF₁ : F ∩ D₁ = J₁)
    (hout₀ : (D₀ \ C).Nonempty) (hout₁ : (D₁ \ C).Nonempty)
    (hfront : frontier C ∩ S ⊆ F) : S ∩ C = F := by
  have hcap {D J : Set M} (hDS : D ⊆ S) (hconn : IsPreconnected (D \ J))
      (hF : F ∩ D = J) (hout : (D \ C).Nonempty) : D ∩ C ⊆ F := by
    intro x hx
    by_contra hxF
    have hxJ : x ∉ J := fun hxJ => hxF (hF.superset hxJ).1
    have havoid : Disjoint (D \ J) (frontier C) := by
      refine disjoint_left.mpr fun z hz hzfront => ?_
      exact hz.2 (hF.subset ⟨hfront ⟨hzfront, hDS hz.1⟩, hz.1⟩)
    have hsub := IsPreconnected.subset_of_disjoint_frontier hconn
      ⟨x, ⟨hx.1, hxJ⟩, hx.2⟩ havoid
    obtain ⟨y, hyD, hyC⟩ := hout
    have hyJ : y ∉ J := fun hyJ => hyC (hFC (hF.superset hyJ).1)
    exact hyC (hsub ⟨hyD, hyJ⟩)
  apply Subset.antisymm
  · intro x hx
    rcases hcover hx.1 with (hx₀ | hx₁) | hxF
    · exact hcap hD₀S hconn₀ hF₀ hout₀ ⟨hx₀, hx.2⟩
    · exact hcap hD₁S hconn₁ hF₁ hout₁ ⟨hx₁, hx.2⟩
    · exact hxF
  · exact subset_inter hFS hFC


theorem subset_or_inter_eq_of_connected_interior {M : Type*} [TopologicalSpace M]
    {A C F : Set M} (hA : IsClosed A) (hreg : closure (interior C) = C)
    (hconn : IsPreconnected (interior C)) (hmeet : frontier A ∩ C = F)
    (hF : F ⊆ frontier C) : C ⊆ A ∨ C ∩ A = F := by
  have havoid : Disjoint (interior C) (frontier A) := by
    refine disjoint_left.mpr fun x hx hxA => ?_
    exact (hF (hmeet.subset ⟨hxA, interior_subset hx⟩)).2 hx
  have hcover : interior C ⊆ interior A ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ interior A
    · exact Or.inl hxA
    · exact Or.inr fun hmem => disjoint_left.mp havoid hx ⟨subset_closure hmem, hxA⟩
  rcases hconn.subset_or_subset isOpen_interior hA.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · exact Or.inl (hreg ▸ closure_minimal (hin.trans interior_subset) hA)
  · have hCA : C ⊆ closure Aᶜ := hreg ▸ closure_mono hout
    refine Or.inr (Subset.antisymm ?_ ?_)
    · intro x hx
      have hxnot : x ∉ interior A := by
        have h := hCA hx.1
        rwa [closure_compl] at h
      exact hmeet.subset ⟨⟨subset_closure hx.2, hxnot⟩, hx.1⟩
    · intro x hx
      have h := hmeet.superset hx
      exact ⟨h.2, hA.frontier_subset h.1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_annular_band_with_filling_trace
    {S A A₀ A₁ J L : Set E} (hS : IsPLSphere 2 S)
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S)
    (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L)
    (hJA : J ⊆ A) (hLA : L ⊆ A) (hJL : Disjoint J L)
    (hJend : Disjoint J (A₀ ∪ A₁)) (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J)
    (hLess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = L) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      ∀ C : Set E, φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C →
        frontier C ∩ S ⊆ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) →
        Disjoint C (A₀ ∪ A₁) → S ∩ C = φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨D₀, D₁, r₀, r₁, φ, hr₀, hr₁, hb₀, hb₁, hD₀S, hD₁S, -, hends,
    hφ, hφA, hzero, hone, hF₀, hF₁, hcover⟩ :=
    hS.exists_annular_band_with_end_caps hA hAS hJ hL hJA hLA hJL hJend hLend hJess hLess
  refine ⟨φ, hφ, hφA, hzero, hone, ?_⟩
  intro C hFC hfront hdis
  have hconn₀ : IsPreconnected (D₀ \ J) := by
    rw [← hb₀]
    exact hr₀.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
  have hconn₁ : IsPreconnected (D₁ \ L) := by
    rw [← hb₁]
    exact hr₁.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
  have hout : (D₀ \ C).Nonempty ∧ (D₁ \ C).Nonempty := by
    obtain ⟨x, hx⟩ := hA.ends_nonempty.1
    obtain ⟨y, hy⟩ := hA.ends_nonempty.2
    have hxC : x ∉ C := fun hxC => disjoint_left.mp hdis hxC (Or.inl hx)
    have hyC : y ∉ C := fun hyC => disjoint_left.mp hdis hyC (Or.inr hy)
    rcases hends with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact ⟨⟨x, h₀ hx, hxC⟩, ⟨y, h₁ hy, hyC⟩⟩
    · exact ⟨⟨y, h₀ hy, hyC⟩, ⟨x, h₁ hx, hxC⟩⟩
  exact inter_eq_band_of_end_caps (hφA.trans hAS) hFC hD₀S hD₁S hcover
    hconn₀ hconn₁ hF₀ hF₁ hout.1 hout.2 hfront

end DifferentialGeometry.Topology.PiecewiseLinear
