import DifferentialGeometry.Geometry.Neck.SeparatingChainCoverage
import DifferentialGeometry.Geometry.Neck.CollarRegularData
import DifferentialGeometry.Topology.Ehresmann.SphereTube

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Affine DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Neck

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_regular_data_of_separating_neck_chain (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀
    {E H W : Type} {F G M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M],
    ∀ (g : SmoothRiemannianMetric J M) (ε : ℝ), 0 ≤ ε → ε < ε₀ →
    ∀ (n : ℕ) [NeZero n] (D : separatingNeckChain I g Cₒ ε n (W := W)),
    let v : Fin (n + 1) → W → ℝ := fun i w ↦
      (D.alignment i).1 * (D.charts i).axial (D.inclusion w) + (D.alignment i).2
    ∃ (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯)
      (horder : ∀ w, Antitone (fun i ↦ θ i w))
      (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
      let χ := orderedStepPartition θ horder hfirst hlast
      (∀ i, tsupport (χ i) ⊆ D.controlledRegion i) ∧
      let u := fun w ↦ ∑ i, χ i w * v i w
      ∃ (b₀ b₁ : ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hb : b₀ < b₁)
        (hbdy : ∀ w, I.IsBoundaryPoint w → u w = b₀ ∨ u w = b₁),
        b₀ = (D.alignment 0).2 ∧ b₁ = (D.alignment (Fin.last n)).2 ∧
        RegularIntervalDatum I u b₀ b₁ ∧
        u ⁻¹' ({b₀} : Set ℝ) = D.lowerEnd ∧ u ⁻¹' ({b₁} : Set ℝ) = D.upperEnd ∧
        (∀ᶠ w in 𝓝ˢ D.lowerEnd, χ 0 w = 1) ∧
        (∀ᶠ w in 𝓝ˢ D.upperEnd, χ (Fin.last n) w = 1) ∧
        (∀ᶠ w in 𝓝ˢ D.lowerEnd, u w = v 0 w) ∧
        (∀ᶠ w in 𝓝ˢ D.upperEnd, u w = v (Fin.last n) w) ∧
        ∃ η₀ : S² ≃ₘ⟮𝓡 2, hI.boundaryI⟯ boundaryLevel u b₀ b₁ hb.ne hu.continuous hbdy,
          (∀ p, D.inclusion (η₀ p).1.1 = ((D.charts 0).chart
            ⟨(p, 0), D.control_domain 0 ⟨mem_univ _, D.control_center 0⟩⟩ : M)) ∧
          ∃ Ψ : (S² × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), I⟯ W,
            (∀ p, u (Ψ p) = b₀ + (b₁ - b₀) * (p.2 : ℝ)) ∧
            (∀ p, D.inclusion (Ψ (p, ⟨0, by norm_num⟩)) = ((D.charts 0).chart
              ⟨(p, 0), D.control_domain 0 ⟨mem_univ _, D.control_center 0⟩⟩ : M)) ∧
            range (D.inclusion ∘ Ψ) ⊆ ⋃ i, D.truncation i := by
  classical
  obtain ⟨ε₁, hε₁, hregular⟩ := exists_regular_data_of_controlled_collar_regions Cₒ hCₒ
  obtain ⟨ε₂, hε₂, hgraphs⟩ := exists_uniform_collar_graphs_of_separating_chain Cₒ hCₒ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro E H W F G M _ _ _ _ I _ _ hI _ _ _ _ _ _ _ _ J _ _ _ _ _
    g ε hεnonneg hε n _ D v
  have hg := hgraphs I J g ε hεnonneg (hε.trans_le (min_le_right _ _)) n D
  obtain ⟨hcontrolled, d, hd, hsegment, hinward⟩ :=
    D.controlled_regions_and_inward_segment (fun j i hi ↦ Classical.choice (hg j i hi))
  specialize hregular (W := W) (M := M) I J
  have hcol (j : Fin n) (p : S²) (t : ℝ) (ht : t ∈ Icc (D.collar j).lower (D.collar j).upper) :
      (p, (D.alignment (D.origin j)).1 * t) ∈ (D.charts (D.origin j)).domain :=
    (D.collar j).contained p t ht
  have hseg (p : S²) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) d) :
      (p, 0 + (D.alignment 0).1 * t) ∈ (D.charts 0).domain := by
    simpa only [separatingNeckChain.alignment, finiteLineAffineAlignment_zero, one_mul, zero_add] using
      hsegment p t ht
  have hin (p : S²) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) d) :
      ((D.charts 0).chart ⟨(p, 0 + (D.alignment 0).1 * t), hseg p t ht⟩ : M) ∈ range D.inclusion := by
    simpa only [separatingNeckChain.alignment, finiteLineAffineAlignment_zero, one_mul, zero_add] using
      hinward p t ht
  have hout := hregular n D.inclusion D.smooth_inclusion D.embedding D.fullRank D.dimension
    g D.charts D.controlledDomain
    (fun i ↦ isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))
    ε hεnonneg (hε.trans_le (min_le_left _ _)) D.metric_close
    D.sign D.edgeTranslation D.sign_unit D.origin D.origin_adjacent
    (fun j ↦ (D.collar j).lower) (fun j ↦ (D.collar j).upper) (fun j ↦ (D.collar j).width)
    hcol D.collar_internal D.lowerSide D.upperSide D.lowerSide_closed D.upperSide_closed D.sides_disjoint
    D.sides_cover (fun j ↦ (D.lowerFace_attach j).le) (fun j ↦ (D.upperFace_attach j).le)
    (fun i j hij ↦ (D.ordered_exteriors i j hij).2.2) hcontrolled
    (by intro j w hw; exact D.overlap_controlled j (D.collar_overlap j hw))
    (fun j w hw ↦ (D.recorded_collar_errors j hw).1)
    (fun j w hw ↦ (D.recorded_collar_errors j hw).2)
    D.lowerEnd D.upperEnd D.boundary (D.lowerEnd_side _) (D.upperEnd_side _)
    0 0 (fun p ↦ D.control_domain 0 ⟨mem_univ p, D.control_center 0⟩)
    (fun p ↦ D.control_domain (Fin.last n) ⟨mem_univ p, D.control_center (Fin.last n)⟩)
    D.lowerEnd_image D.upperEnd_image d hd hseg hin
  obtain ⟨θ, horder, hfirst, hlast, hsupp, hu, hb, hbdy, hdata, hf₀, hf₁, hw₀, hw₁, he₀, he₁,
    η₀, hη₀, Ψ, hheight, hlower⟩ := hout
  refine ⟨θ, horder, hfirst, hlast, hsupp, _, _, hu, hb, hbdy, ?_, ?_, hdata, hf₀, hf₁, hw₀, hw₁, he₀, he₁,
    η₀, hη₀, Ψ, hheight, hlower, ?_⟩
  · simp only [mul_zero, zero_add]
    rfl
  · simp only [mul_zero, zero_add]
    rfl
  · rintro _ ⟨p, rfl⟩
    exact D.truncation_cover ⟨Ψ p, rfl⟩

end DifferentialGeometry.Geometry.Neck
