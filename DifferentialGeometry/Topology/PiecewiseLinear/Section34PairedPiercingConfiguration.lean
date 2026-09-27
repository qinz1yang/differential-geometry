import DifferentialGeometry.Topology.PiecewiseLinear.Section34SimultaneousEmptyBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorInnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InwardPreparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def Section34PairedCancellationConfiguration {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (A As B Bs T : Set M) (k : ℕ) (J : ℕ → Set M) : Prop :=
    (∃ i < k, ∃ D : Set M, IsPLCellOn 2 D (J i) ∧
      D ⊆ B ∩ interior T ∧ D ∩ As = J i ∧ IsConnected (D \ J i)) ∨
    ∃ i < k, ∃ j < k, i ≠ j ∧
      (¬ ∃ D : Set M, IsPLCellOn 2 D (J i) ∧ D ⊆ B) ∧
      (¬ ∃ D : Set M, IsPLCellOn 2 D (J j) ∧ D ⊆ B) ∧
      ∃ (F : Set M) (P : Set (EuclideanSpace ℝ (Fin 3)))
        (u : EuclideanSpace ℝ (Fin 3) → M)
        (g : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsAnnulusOn F (J i) (J j) ∧ F ⊆ A ∧ Disjoint (F \ (J i ∪ J j)) Bs ∧
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
        IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B ∩ interior T ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) = J i ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) = J j ∧
        Disjoint ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) As

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

theorem exists_section34_paired_interior_cancellation_configuration
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (hlt : 1 < cnt e)
    (hanchors : ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
        (∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
        ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) :
    Section34PairedCancellationConfiguration (G (ends e).1 '' Aa e)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' Bb e)
      (G (ends e).2 '' CpBd (ends e).2) (Tp e) (cnt e) (Pg e) := by
  classical
  by_cases hexists : ∃ i < cnt e, ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e
  · obtain ⟨i, D, hi, hD, hDT, htrace, hconn⟩ :=
      exists_section34_interior_innermost_disk hprep hpack e hanchors hexists
    exact Or.inl ⟨i, hi, D, hD, hDT, htrace, hconn⟩
  · have hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
        IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e := by
      exact fun i hi hD => hexists ⟨i, hi, hD⟩
    obtain ⟨i, hi, j, hj, hij, hiess, hjess, F, P, u, g, hF, hFA, hFempty, hP, hu, -, hg,
      hgP, hDT, hzero, hone, hempty⟩ :=
      exists_section34_simultaneous_empty_bands hprep hpack e hlt hanchors hess
    exact Or.inr ⟨i, hi, j, hj, hij, hiess, hjess, F, P, u, g, hF, hFA, hFempty, hP, hu,
      hg, hgP, hDT, hzero, hone, hempty⟩

theorem exists_section34_inward_paired_cancellation_configuration
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (hlt : 1 < cnt e) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G' ∧
      (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e)}) ∧
      (∀ d, d ≠ e → G' (ends d).1 '' Aa d = G (ends d).1 '' Aa d ∧
        G' (ends d).2 '' Bb d = G (ends d).2 '' Bb d) ∧
      Section34PairedCancellationConfiguration (G' (ends e).1 '' Aa e)
        (G' (ends e).1 '' CpBd (ends e).1) (G' (ends e).2 '' Bb e)
        (G' (ends e).2 '' CpBd (ends e).2) (Tp e) (cnt e) (Pg e) := by
  obtain ⟨G', hpack', hoff, hann, hanchors⟩ := exists_section34_inward_preparation hprep hpack e
  exact ⟨G', hpack', hoff, hann,
    exists_section34_paired_interior_cancellation_configuration hprep hpack' e hlt hanchors⟩

end DifferentialGeometry.Topology.PiecewiseLinear
