import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization

set_option autoImplicit false

open Set Metric Real
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem exists_open_distanceCoordinates_of_pointwise_packet
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω : Set X} {a b : ι → X} {q : X} {δ : ℝ}
    (hpoint : PairedComparisonPacket (δ / 2) {q} a b)
    (hcomp : fourPointComparison 1 Ω) (hΩ : Ω ∈ 𝓝 q)
    (hanchors : range a ∪ range b ⊆ Ω)
    (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R)) :
    ∃ V : Set X, IsOpen V ∧ q ∈ V ∧ V ⊆ Ω ∧ PairedComparisonPacket δ V a b ∧
      (∃ a₀ A : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧
        ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A) ∧
      IsOpenMap (fun z : V => distanceCoordinates 1 a (z : X)) ∧
      IsOpenMap (fun z : V => distanceCoordinates 2 a (z : X)) ∧
      LipschitzWith (Fintype.card ι) (fun z : V => distanceCoordinates 1 a (z : X)) ∧
      LipschitzWith (NNReal.sqrt (Fintype.card ι)) (fun z : V => distanceCoordinates 2 a (z : X)) ∧
      (Fintype.card ι : ℝ≥0∞) ≤ dimH V := by
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hmul := (le_div_iff₀ (show 0 < 100 * (Fintype.card ι : ℝ) by positivity)).mp hδm
  have hquality : δ / 2 < Real.pi / 2 := by nlinarith [Real.two_le_pi]
  have hne := hpoint.not_mem_anchors (by simp : q ∈ ({q} : Set X)) hquality
  obtain ⟨V, hVopen, hq, hV, hpacket, a₀, A, ha₀, haA, hbounds⟩ :=
    hpoint.exists_uniform_nhds hδ hne hΩ
  have hopen1 := hpacket.isOpenMap_distanceCoordinates_one hcurves hcomp hV hVopen hanchors
    ha₀ hδ hδm (fun z hz => hcomplete z (hV hz)) hbounds
  have hopen2 := hpacket.isOpenMap_distanceCoordinates hcurves hcomp hV hVopen hanchors
    ha₀ hδ hδm (fun z hz => hcomplete z (hV hz)) hbounds 2
  have hLip1 : LipschitzWith (Fintype.card ι) (fun z : V => distanceCoordinates 1 a (z : X)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (lipschitzWith_distanceCoordinates_one a).dist_le_mul x y
  have hLip2 : LipschitzWith (NNReal.sqrt (Fintype.card ι)) (fun z : V => distanceCoordinates 2 a (z : X)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (lipschitzWith_distanceCoordinates_two a).dist_le_mul x y
  refine ⟨V, hVopen, hq, hV, hpacket, ⟨a₀, A, ha₀, haA, hbounds⟩, hopen1, hopen2, hLip1, hLip2, ?_⟩
  have himage : (fun z : V => distanceCoordinates 1 a (z : X)) '' univ = distanceCoordinates 1 a '' V := by
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, mem_univ _, rfl⟩
  have hIopen : IsOpen (distanceCoordinates 1 a '' V) := by
    rw [← himage]
    exact hopen1 univ isOpen_univ
  apply card_le_dimH_of_distanceCoordinates_image_has_interior 1 a
  rw [hIopen.interior_eq]
  exact ⟨distanceCoordinates 1 a q, q, hq, rfl⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
