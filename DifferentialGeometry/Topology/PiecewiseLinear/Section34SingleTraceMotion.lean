import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialSubfamilyMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierBandDescent

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_single_trace_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (k : Fin (cnt e)) (K : Set M₂) (ψ : M₂ ≃ₜ M₂),
      IsCompact K ∧ K ⊆ interior (Sp e) ∧ EqOn ψ id Kᶜ ∧
      IsPLOn 3 3 ψ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      Disjoint K (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
      Disjoint K (Pg e k.val) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ ψ '' (G (ends e).2 '' CpBd (ends e).2) = Pg e k.val := by
  obtain ⟨I, -, -, hcarry, K₀, Ψ, hK₀, hK₀S, hfix₀, hΨ, hArim₀, hBrim₀, hout₀,
      hkeep₀, -, htrace₀⟩ := exists_section34_essential_subfamily_motion hprep hpack e
  obtain ⟨k, K, Φ, hK, hKS, hfix, hΦ, hArim, hBrim, hout, hkeep, -, -, htrace⟩ :=
    exists_section34_single_carrier_trace_of_current_family hprep hpack e I Ψ hK₀ hK₀S
      hfix₀ hΨ hArim₀ hBrim₀ hout₀ hkeep₀ hcarry htrace₀
  exact ⟨k.1, K, Φ, hK, hKS, hfix, hΦ, hArim, hBrim, hout, hkeep, htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
