import DifferentialGeometry.Topology.FundamentalGroup.Sigma
set_option autoImplicit false
noncomputable section
open Set
namespace GC.Topology
universe u v

theorem surjective_fundamentalGroup_sigmaMk {ι : Type u} (X : ι → Type v)
    [∀ i, TopologicalSpace (X i)] (i : ι) (x₀ : X i) :
    Function.Surjective (FundamentalGroup.map
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) x₀) := by
  classical
  let r : C((Σ j, X j), X i) :=
    { toFun := fun p => if h : p.fst = i then h ▸ p.snd else x₀
      continuous_toFun := by
        apply continuous_sigma
        intro j
        by_cases h : j = i
        · subst j
          simp only
          exact continuous_id
        · simp only [dif_neg h]
          exact continuous_const }
  intro p
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
      have hγ (t) : γ t ∈ range (Sigma.mk i : X i → Σ j, X j) := by
        have hsub := (isConnected_range γ.continuous).isPreconnected.subset_isClopen
          isClopen_range_sigmaMk
          (show (range γ ∩ range (Sigma.mk i : X i → Σ j, X j)).Nonempty from
            ⟨⟨i, x₀⟩, γ.source_mem_range, ⟨x₀, rfl⟩⟩)
        exact hsub ⟨t, rfl⟩
      have hr₀ : r (⟨i, x₀⟩ : Σ j, X j) = x₀ := by simp [r]
      let δ : Path x₀ x₀ := (γ.map r.continuous).cast hr₀.symm hr₀.symm
      refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
      change Path.Homotopic.Quotient.mk (δ.map continuous_sigmaMk) =
        Path.Homotopic.Quotient.mk γ
      congr 1
      apply Path.ext
      funext t
      obtain ⟨z, hz⟩ := hγ t
      change (⟨i, r (γ t)⟩ : Σ j, X j) = γ t
      rw [← hz]
      simp [r]

def fundamentalGroupSigmaEquiv {ι : Type u} (X : ι → Type v)
    [∀ i, TopologicalSpace (X i)] (i : ι) (x₀ : X i) :
    FundamentalGroup (X i) x₀ ≃* FundamentalGroup (Σ j, X j) ⟨i, x₀⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map
    (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) x₀)
    ⟨DifferentialGeometry.Topology.injective_fundamentalGroup_sigmaMk X i x₀,
      surjective_fundamentalGroup_sigmaMk X i x₀⟩

end GC.Topology
