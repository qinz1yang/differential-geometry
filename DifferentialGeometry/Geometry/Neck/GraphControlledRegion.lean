import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Topology.Manifold.OrientedProductChart
import DifferentialGeometry.Topology.Embedding.GraphCollarCover
import DifferentialGeometry.Topology.Embedding.ProductChartInwardSegment
import DifferentialGeometry.Topology.Connected.EndpointCollarStrip
import Mathlib.Order.Interval.Set.OrdConnected

noncomputable section
open Set Topology
open scoped Manifold ContDiff
open Poincare.Topology Poincare.Topology.Manifold Poincare.Topology.Embedding

namespace Poincare.Geometry.Neck

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private instance : PathConnectedSpace S² :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank] :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) _ zero_le_one)

private theorem signed_interval_mem {B : Set ℝ} (hB : OrdConnected B)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {a b t : ℝ}
    (ha : σ * a ∈ B) (hb : σ * b ∈ B) (ht : a ≤ t ∧ t ≤ b) : σ * t ∈ B := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at *
    exact hB.out ha hb ht
  · apply hB.out hb ha
    constructor <;> linarith only [ht.1, ht.2]

private theorem range_graph_eq {N : Type*} (a : N → ℝ) :
    range (fun p ↦ (p, a p)) = {x : N × ℝ | x.2 = a x.1} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rfl
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem oriented_image_eq (C : cylindricalChart J (M := M))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (O : TopologicalSpace.Opens (S² × ℝ))
    (hO : ∀ x : S² × ℝ, x ∈ O ↔ (x.1, σ * x.2) ∈ C.domain)
    (Φ : O ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ C.target)
    (hΦ : ∀ x : O, Φ x = C.chart ⟨((x : S² × ℝ).1, σ * (x : S² × ℝ).2),
      (hO x).mp x.property⟩) (B : Set (S² × ℝ)) :
    (fun x : O ↦ (Φ.toHomeomorph x : M)) '' ((Subtype.val : O → S² × ℝ) ⁻¹' B) =
      C.region {x | (((x : C.domain) : S² × ℝ).1, σ * (x : S² × ℝ).2) ∈ B} := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [cylindricalChart.region, image_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨((x : S² × ℝ).1, σ * (x : S² × ℝ).2), (hO x).mp x.property⟩, ?_, ?_⟩
    · change ((x : S² × ℝ).1, σ * (σ * (x : S² × ℝ).2)) ∈ B
      rw [← mul_assoc, hσσ, one_mul]
      exact hx
    · exact congrArg Subtype.val (hΦ x).symm
  · rintro ⟨x, hx, rfl⟩
    have hm : ((x : S² × ℝ).1, σ * (x : S² × ℝ).2) ∈ O := by
      apply (hO _).mpr
      change ((x : S² × ℝ).1, σ * (σ * (x : S² × ℝ).2)) ∈ C.domain
      rw [← mul_assoc, hσσ, one_mul]
      exact x.property
    refine ⟨⟨((x : S² × ℝ).1, σ * (x : S² × ℝ).2), hm⟩, hx, ?_⟩
    change (Φ ⟨((x : S² × ℝ).1, σ * (x : S² × ℝ).2), hm⟩ : M) = (C.chart x : M)
    rw [hΦ]
    apply congrArg (fun z : C.domain ↦ (C.chart z : M))
    apply Subtype.ext
    change ((x : S² × ℝ).1, σ * (σ * (x : S² × ℝ).2)) = (x : S² × ℝ)
    rw [← mul_assoc, hσσ, one_mul]

theorem cylindricalChart.between_subset_controlled_of_signed_graph_collars
    {W : Type*} [TopologicalSpace W] [PreconnectedSpace W] [T2Space M]
    (C : cylindricalChart J (M := M)) (ι : W → M) (hι : Continuous ι)
    (hinj : Function.Injective ι)
    (P₀ K₀ Q₀ P₁ K₁ Q₁ : Set W)
    (hP₀ : IsClosed P₀) (hK₀ : IsClosed K₀) (hQ₀ : IsClosed Q₀)
    (hP₁ : IsClosed P₁) (hK₁ : IsClosed K₁) (hQ₁ : IsClosed Q₁)
    (hcover₀ : P₀ ∪ K₀ ∪ Q₀ = univ) (hcover₁ : P₁ ∪ K₁ ∪ Q₁ = univ)
    (hdisj₀ : Disjoint P₀ Q₀) (hdisj₁ : Disjoint P₁ Q₁)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (a b c d : S² → ℝ) (ha : Continuous a) (hd : Continuous d)
    (hab : ∀ p, a p < b p) (hbc : ∀ p, b p < c p) (hcd : ∀ p, c p < d p)
    (B : Set ℝ) (hB : OrdConnected B)
    (hBa : ∀ p, σ * a p ∈ B) (hBd : ∀ p, σ * d p ∈ B)
    (hsource : ∀ p : S², ∀ t ∈ B, (p, t) ∈ C.domain)
    (himage₀ : ι '' K₀ = C.region {x | a (x : S² × ℝ).1 ≤ σ * (x : S² × ℝ).2 ∧
      σ * (x : S² × ℝ).2 ≤ b (x : S² × ℝ).1})
    (himage₁ : ι '' K₁ = C.region {x | c (x : S² × ℝ).1 ≤ σ * (x : S² × ℝ).2 ∧
      σ * (x : S² × ℝ).2 ≤ d (x : S² × ℝ).1})
    (hleft : C.region {x | σ * (x : S² × ℝ).2 = a (x : S² × ℝ).1} ⊆ ι '' (P₀ ∩ K₀))
    (hright : C.region {x | σ * (x : S² × ℝ).2 = d (x : S² × ℝ).1} ⊆ ι '' (K₁ ∩ Q₁)) :
    (interior P₀)ᶜ ∩ (interior Q₁)ᶜ ⊆
      ι ⁻¹' C.region {x | (x : S² × ℝ).2 ∈ B} := by
  obtain ⟨O, hO, Φ, hΦ, _⟩ := exists_oriented_product_chart C.domain C.target C.chart σ hσ
  have himage := oriented_image_eq C σ hσ O hO Φ hΦ
  obtain ⟨p₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (univ_nonempty : (univ : Set S²).Nonempty) ha.continuousOn
  obtain ⟨p₁, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (univ_nonempty : (univ : Set S²).Nonempty) hd.continuousOn
  have htrunc : (univ : Set S²) ×ˢ Icc (a p₀) (d p₁) ⊆ O := by
    rintro x ⟨_, hx⟩
    exact (hO x).mpr (hsource x.1 _ (signed_interval_mem hB σ hσ (hBa p₀) (hBd p₁) hx))
  have hbetween := (cover_and_between_subset_of_chart_graph_collars ι hι hinj
    P₀ K₀ Q₀ P₁ K₁ Q₁ hP₀ hK₀ hQ₀ hP₁ hK₁ hQ₁ hcover₀ hcover₁ hdisj₀ hdisj₁
    O C.target Φ.toHomeomorph a b c d ha hd hab hbc hcd (a p₀) (d p₁)
    (fun p ↦ hmin (mem_univ p)) (fun p ↦ hmax (mem_univ p)) htrunc
    (by rw [himage]; exact himage₀) (by rw [himage]; exact himage₁)
    (by rw [range_graph_eq, himage]; exact hleft)
    (by rw [range_graph_eq, himage]; exact hright)).2.1
  intro w hw
  have hwD := hbetween hw
  rw [himage] at hwD
  obtain ⟨y, ⟨x, hx, rfl⟩, hxy⟩ := hwD
  refine ⟨C.chart x, ⟨x, ?_, rfl⟩, hxy⟩
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have ht := signed_interval_mem hB σ hσ (hBa (x : S² × ℝ).1) (hBd (x : S² × ℝ).1) hx
  change (x : S² × ℝ).2 ∈ B
  simpa only [← mul_assoc, hσσ, one_mul] using ht

private theorem full_graph_image_eq_range
    {N Y : Type*} [TopologicalSpace N] [TopologicalSpace Y]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens Y)
    (Φ : O ≃ₜ V) (a : N → ℝ) (hmem : ∀ p, (p, a p) ∈ O) :
    (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x | x.2 = a x.1}) =
        range (fun p ↦ (Φ ⟨(p, a p), hmem p⟩ : Y)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : N × ℝ).1, ?_⟩
    apply congrArg (fun z : O ↦ (Φ z : Y))
    exact Subtype.ext (Prod.ext rfl hx.symm)
  · rintro ⟨p, rfl⟩
    exact ⟨⟨(p, a p), hmem p⟩, rfl, rfl⟩

private theorem endpoint_graph_wedge
    {W Y N : Type*} [TopologicalSpace W] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace N] [CompactSpace N] [Nonempty N]
    (ι : W → Y) (hι : _root_.Topology.IsClosedEmbedding ι)
    (hregular : closure (interior (range ι)) = range ι)
    (hconnected : IsPreconnected (interior (range ι)))
    (P K Q : Set W) (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (hinternal : ι '' K ⊆ interior (range ι))
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens Y) (Φ : O ≃ₜ V)
    (t₀ : ℝ) (a b : N → ℝ) (hb : Continuous b)
    (h₀a : ∀ p, t₀ < a p) (hab : ∀ p, a p < b p)
    (hstrip : {x : N × ℝ | t₀ ≤ x.2 ∧ x.2 ≤ b x.1} ⊆ O)
    (hcenter : range (fun p ↦
      (Φ ⟨(p, t₀), hstrip ⟨le_rfl, ((h₀a p).trans (hab p)).le⟩⟩ : Y)) ⊆ frontier (range ι))
    (hcollar : ι '' K = (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}))
    (hfar : range (fun p ↦
      (Φ ⟨(p, b p), hstrip ⟨((h₀a p).trans (hab p)).le, le_rfl⟩⟩ : Y)) ⊆ ι '' (K ∩ Q)) :
    (interior Q)ᶜ ⊆ ι ⁻¹' ((fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x | t₀ ≤ x.2 ∧ x.2 ≤ b x.1})) := by
  let A : Set (N × ℝ) := {x | t₀ ≤ x.2 ∧ x.2 ≤ b x.1}
  let D := (fun x : O ↦ (Φ x : Y)) '' ((Subtype.val : O → N × ℝ) ⁻¹' A)
  have hAc : IsCompact A := isCompact_graphBand (fun _ ↦ t₀) b
    continuous_const hb (fun p ↦ (h₀a p).trans (hab p))
  have hDc : IsClosed D :=
    ((_root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hAc
      (fun x hx ↦ ⟨⟨x, hstrip hx⟩, rfl⟩)).image
        (continuous_subtype_val.comp Φ.continuous)).isClosed
  have hKD : ι '' K ⊆ D := by
    rw [hcollar]
    apply image_mono
    intro x hx
    exact ⟨(h₀a (x : N × ℝ).1).le.trans hx.1, hx.2⟩
  have hfront : frontier D ⊆ frontier (range ι) ∪ ι '' (K ∩ Q) := by
    rw [frontier_graphBand_of_opens_product_chart O V Φ (fun _ ↦ t₀) b
      continuous_const hb (fun p ↦ (h₀a p).trans (hab p)) hstrip]
    exact union_subset_union hcenter hfar
  have hne : (K ∩ Q).Nonempty := by
    let p : N := Classical.choice inferInstance
    obtain ⟨w, hw, _⟩ := hfar ⟨p, rfl⟩
    exact ⟨w, hw⟩
  exact (cover_and_endpoint_subset_of_embedded_collar ι hι hregular hconnected P K Q D
    hP hK hQ hcover hdisj hDc hKD hinternal hfront hne).2

theorem cylindricalChart.endpoint_subset_controlled_and_inward_of_signed_graph_collar
    {W : Type*} [TopologicalSpace W] [T2Space M]
    (C : cylindricalChart J (M := M)) (ι : W → M)
    (hι : _root_.Topology.IsClosedEmbedding ι)
    (hregular : closure (interior (range ι)) = range ι)
    (hconnected : IsPreconnected (interior (range ι)))
    (P K Q : Set W) (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (Sminus Splus : Set W)
    (hboundary : frontier (range ι) = ι '' Sminus ∪ ι '' Splus)
    (hplusQ : Splus ⊆ Q) (hinternal : ι '' K ⊆ interior (range ι))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (t₀ : ℝ) (a b : S² → ℝ) (ha : Continuous a) (hb : Continuous b)
    (h₀a : ∀ p, t₀ < a p) (hab : ∀ p, a p < b p)
    (B : Set ℝ) (hB : OrdConnected B) (hB₀ : σ * t₀ ∈ B) (hBb : ∀ p, σ * b p ∈ B)
    (hsource : ∀ p : S², ∀ t ∈ B, (p, t) ∈ C.domain)
    (hminus : ι '' Sminus = C.region {x | σ * (x : S² × ℝ).2 = t₀})
    (hcollar : ι '' K = C.region {x | a (x : S² × ℝ).1 ≤ σ * (x : S² × ℝ).2 ∧
      σ * (x : S² × ℝ).2 ≤ b (x : S² × ℝ).1})
    (hfar : ι '' (K ∩ Q) = C.region {x | σ * (x : S² × ℝ).2 = b (x : S² × ℝ).1}) :
    (interior Q)ᶜ ⊆ ι ⁻¹' C.region {x | (x : S² × ℝ).2 ∈ B} ∧
      ∃ d : ℝ, 0 < d ∧
        ∃ hsegment : ∀ p : S², ∀ t ∈ Icc (0 : ℝ) d, (p, σ * (t₀ + t)) ∈ C.domain,
          ∀ p t (ht : t ∈ Icc (0 : ℝ) d),
            (C.chart ⟨(p, σ * (t₀ + t)), hsegment p t ht⟩ : M) ∈ range ι := by
  obtain ⟨O, hO, Φ, hΦ, _⟩ := exists_oriented_product_chart C.domain C.target C.chart σ hσ
  have himage := oriented_image_eq C σ hσ O hO Φ hΦ
  have hstrip : {x : S² × ℝ | t₀ ≤ x.2 ∧ x.2 ≤ b x.1} ⊆ O := by
    intro x hx
    exact (hO x).mpr (hsource x.1 _ (signed_interval_mem hB σ hσ hB₀ (hBb x.1) hx))
  have hface (f : S² → ℝ) (hf : ∀ p, (p, f p) ∈ O) :
      C.region {x | σ * (x : S² × ℝ).2 = f (x : S² × ℝ).1} =
        range (fun p ↦ (Φ.toHomeomorph ⟨(p, f p), hf p⟩ : M)) :=
    (himage {x | x.2 = f x.1}).symm.trans
      (full_graph_image_eq_range O C.target Φ.toHomeomorph f hf)
  have hminus' := hminus.trans (hface (fun _ ↦ t₀)
    (fun p ↦ hstrip ⟨le_rfl, ((h₀a p).trans (hab p)).le⟩))
  have hfar' := hfar.trans (hface b
    (fun p ↦ hstrip ⟨((h₀a p).trans (hab p)).le, le_rfl⟩))
  have hcollar' : ι '' K = (fun x : O ↦ (Φ.toHomeomorph x : M)) ''
      ((Subtype.val : O → S² × ℝ) ⁻¹' {x | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}) := by
    rw [himage]
    exact hcollar
  have hwedge := endpoint_graph_wedge ι hι hregular hconnected P K Q hP hK hQ hcover hdisj
    hinternal O C.target Φ.toHomeomorph t₀ a b hb h₀a hab hstrip
    (by rw [← hminus', hboundary]; exact subset_union_left) hcollar' hfar'.symm.le
  refine ⟨?_, ?_⟩
  · intro w hw
    have hwD := hwedge hw
    rw [himage] at hwD
    obtain ⟨y, ⟨x, hx, rfl⟩, hxy⟩ := hwD
    refine ⟨C.chart x, ⟨x, ?_, rfl⟩, hxy⟩
    have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have ht := signed_interval_mem hB σ hσ hB₀ (hBb (x : S² × ℝ).1) hx
    change (x : S² × ℝ).2 ∈ B
    simpa only [← mul_assoc, hσσ, one_mul] using ht
  · obtain ⟨d, hd, hseg, hin⟩ := exists_inward_segment_of_graph_chart_endpoint ι hι
      P K Q hP hK hQ hcover hdisj Sminus Splus hboundary hplusQ hinternal
      O C.target Φ.toHomeomorph t₀ a b ha hb h₀a hab hstrip hminus' hcollar' hfar'.le
    have hm (p : S²) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) d) : (p, t₀ + t) ∈ O :=
      hseg ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩
    refine ⟨d, hd, (fun p t ht ↦ (hO _).mp (hm p t ht)), ?_⟩
    intro p t ht
    have h := hin p (t₀ + t) (by constructor <;> linarith [ht.1, ht.2])
    change (Φ ⟨(p, t₀ + t), hm p t ht⟩ : M) ∈ range ι at h
    rw [hΦ] at h
    exact h

end Poincare.Geometry.Neck
