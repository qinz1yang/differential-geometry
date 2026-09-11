import DifferentialGeometry.Topology.Morse.BoundaryExcellentSublevels
import DifferentialGeometry.Topology.Manifold.Boundary.SublevelDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Morse
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_relative_excellent_morse_sublevel_diffeomorph (b : ℝ) :
    ∃ (f : M → ℝ) (a t c₀ : ℝ) (W : TopologicalSpace.Opens M)
      (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
      (hreg : ∀ x, f x = c₀ → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
      (hi : {x | f x ≤ c₀} ⊆ (𝓡∂ (n + 1)).interior M),
      let _ := DifferentialGeometry.Manifold.RegularLevel.interiorSublevelChartedSpace (𝓡∂ (n + 1))
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hi
      ∃ d : M ≃ₘ⟮𝓡∂ (n + 1), morseModelWithCornersHalfSpace n⟯ {x : M // f x ≤ c₀},
        a < t ∧ t < c₀ ∧ c₀ < b ∧
        (∀ x, a < f x ∧ f x ≤ b) ∧ f ⁻¹' Iic a = ∅ ∧
        f ⁻¹' {b} = (𝓡∂ (n + 1)).boundary M ∧
        (𝓡∂ (n + 1)).boundary M ⊆ W ∧ f ⁻¹' Icc c₀ b ⊆ W ∧
        (∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
          (𝓡∂ (n + 1)).IsInteriorPoint x ∧
          IsNondegenerateCriticalPointAt (𝓡∂ (n + 1)) f x ∧ f x < t) ∧
        {x : M | IsCriticalPointAt (𝓡∂ (n + 1)) f x}.Finite ∧
        InjOn f {x | IsCriticalPointAt (𝓡∂ (n + 1)) f x} ∧
        (∀ x, f x ≤ t → (d x : M) = x) ∧
        (∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
          (fun y => (d y : M)) =ᶠ[𝓝 x] id) ∧
        (∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, f (d p : M) = c₀) ∧
        ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
          ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
            (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
          IsCompact (tsupport V) ∧
          (∀ y ∈ W, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ)) ∧
          ∀ y : BoundaryManifold (𝓡∂ (n + 1)) M,
            0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V y) := by
  obtain ⟨f, a, t, W, hf, hat, htb, hbound, hempty, hlevel, hBW, hband,
    hcrit, _, hfinite, hinj, _, V, hV, hVc, hunit, hVpos⟩ :=
    exists_relative_excellent_morse_sublevel_thresholds (M := M) (n := n + 1) b
  have hboundary (p : BoundaryManifold (𝓡∂ (n + 1)) M) : f p = b := by
    have hh : (p : M) ∈ f ⁻¹' {b} := hlevel.symm ▸ p.property
    exact mem_singleton_iff.mp hh
  have hinterior : ∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → f x < b := by
    intro x hx
    apply lt_of_le_of_ne (hbound x).2
    intro he
    have hb : x ∈ (𝓡∂ (n + 1)).boundary M := hlevel ▸ (show x ∈ f ⁻¹' {b} from he)
    exact ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb
  obtain ⟨c₀, htc, hcb, _, hreg, hi, d, hfix, hdb⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_regular_top_sublevel_diffeomorph
      hV hVpos W hBW hf hboundary hinterior hunit htb
  refine ⟨f, a, t, c₀, W, hf, hreg, hi, d, hat, htc, hcb, hbound, hempty,
    hlevel, hBW, ?_, hcrit, hfinite, hinj, hfix, ?_, hdb, V, hV, hVc, hunit, hVpos⟩
  · intro x hx
    exact hband ⟨htc.le.trans hx.1, hx.2⟩
  · intro x hx
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (hcrit x hx).2.2)] with y hy
    exact hfix y (show f y ≤ t from hy.le)

end DifferentialGeometry.Morse
