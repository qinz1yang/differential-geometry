import DifferentialGeometry.Geometry.Collapse.CurvatureScaleMaximalSelection
import DifferentialGeometry.Geometry.Comparison.Volume.RicciScalePacketFamily

/-!
# LC87 producer piece P1 at the curvature scale (consumer)

`exists_fin_packet_family_of_ricci_bound` (`Geometry/Comparison/Volume/RicciScalePacketFamily.lean`)
bound to the actual curvature scale `ρ p = c R_p` of a smooth metric on a compact connected
manifold, every ball a `g`-ball.  For an ARBITRARY packet type: if every point of a stratum `S`
carries a packet centred there whose plateau contains `B(p, 4 a ρ(p))` and whose domain lies in
`B(p, C ρ(p))`, a finite `Fin`-indexed family of such packets has distinct centres in `S`,
disjoint selection balls, plateaus covering `S` and bounded domain multiplicity — the cover and
overlap fields of LC87 for one family.

* `exists_fin_packet_family_curvatureScale`: general `c, a, C` with `c a ≤ 1/100`, `c C ≤ 1/4`.
* `closedThreeManifold_fin_packet_family`: on an actual connected closed oriented 3-manifold with
  somewhere negative sectional curvature, plateaus `⊇ B(p, R_p/75)`, domains `⊆ B(p, R_p/100)`,
  multiplicity at most `V_{-q²}(11/3) / V_{-q²}(1/3)`, `q = 3/11`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Topology
open Bundle Set
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]

/-- LC87 P1 at the curvature scale `ρ p = c R_p`, every ball a `g`-ball. -/
theorem exists_fin_packet_family_curvatureScale
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤) (S : Set M)
    {c a C : ℝ} (hc : 0 < c) (ha : 0 < a) (hC : 0 ≤ C)
    (hsel : c * a ≤ 1 / 100) (hover : c * C ≤ 1 / 4)
    {Pk : Type*} (center : Pk → M) (plateau domain : Pk → Set M)
    (hpacket : ∀ p ∈ S, ∃ P : Pk, center P = p ∧
      riemannianBallOf g p (4 * a * (c * (curvatureRadius g p).toReal)) ⊆ plateau P ∧
      domain P ⊆ riemannianBallOf g p (C * (c * (curvatureRadius g p).toReal))) :
    let ρ : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    let q : ℝ := (3 * C + 2 * a)⁻¹
    ∃ (n : ℕ) (F : Fin n → Pk), (∀ k, center (F k) ∈ S) ∧
      Function.Injective (fun k => center (F k)) ∧
      Pairwise (fun k l => Disjoint (riemannianBallOf g (center (F k)) (a * ρ (center (F k))))
        (riemannianBallOf g (center (F l)) (a * ρ (center (F l))))) ∧
      S ⊆ ⋃ k, plateau (F k) ∧
      ∀ x : M, (({k | x ∈ domain (F k)} : Set (Fin n)).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  intro ρ q
  let := inducedMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
  have := hRM
  have := hcont
  have hLip : LipschitzWith ⟨c, hc.le⟩ ρ :=
    inducedMetricSpace_lipschitzWith_iff.2 (abs_curvatureScale_sub_le g hfin hc.le)
  have hD : 0 < 3 * C + 2 * a := by positivity
  have hDc : (3 * C + 2 * a) * c < 1 := by nlinarith
  have hpacket' : ∀ p ∈ S, ∃ P : Pk, center P = p ∧
      Metric.ball p (4 * a * ρ p) ⊆ plateau P ∧ domain P ⊆ Metric.ball p (C * ρ p) := by
    intro p hp
    simp only [inducedMetricSpace_ball g]
    exact hpacket p hp
  have h := exists_fin_packet_family_of_ricci_bound g hEnorm S hLip
    (fun p => mul_pos hc (toReal_curvatureRadius_pos g (hfin p))) ha hC (inv_nonneg.mpr hD.le)
    (show c * a ≤ 1 / 2 by linarith) hover (fun p _ => by
      rw [inducedMetricSpace_ball g]
      exact ricciBoundedBelowOn_curvatureScale g (hfin p) hc hD hDc)
    center plateau domain hpacket'
  simp only [inducedMetricSpace_ball g] at h
  exact h

end Inner

/-- LC87 P1 on an actual connected closed oriented 3-manifold with somewhere negative sectional
curvature: plateaus containing `B(p, R_p/75)` and domains inside `B(p, R_p/100)` at every point of
`S` give a finite family with disjoint `R/300`-balls, plateaus covering `S` and domain multiplicity
at most `V_{-q²}(11/3) / V_{-q²}(1/3)`, `q = 3/11`. -/
theorem closedThreeManifold_fin_packet_family
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) (S : Set M.Carrier)
    {Pk : Type*} (center : Pk → M.Carrier) (plateau domain : Pk → Set M.Carrier)
    (hpacket : ∀ p ∈ S, ∃ P : Pk, center P = p ∧
      riemannianBallOf g p ((curvatureRadius g p).toReal / 75) ⊆ plateau P ∧
      domain P ⊆ riemannianBallOf g p ((curvatureRadius g p).toReal / 100)) :
    ∃ (n : ℕ) (F : Fin n → Pk), (∀ k, center (F k) ∈ S) ∧
      Function.Injective (fun k => center (F k)) ∧
      Pairwise (fun k l =>
        Disjoint (riemannianBallOf g (center (F k)) ((curvatureRadius g (center (F k))).toReal / 300))
          (riemannianBallOf g (center (F l)) ((curvatureRadius g (center (F l))).toReal / 300))) ∧
      S ⊆ ⋃ k, plateau (F k) ∧
      ∀ x : M.Carrier, (({k | x ∈ domain (F k)} : Set (Fin n)).ncard : ℝ) ≤
        modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (11 / 3) /
          modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (1 / 3) := by
  have := closedOrientedManifold_t2Space_tangentBundle M.toClosedOrientedManifold
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  have hfin := curvatureRadius_ne_top_of_not_sectionalBoundedBelow hneg
  have h1 (p : M.Carrier) : 1 / 3 * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 300 := by ring
  have h2 (p : M.Carrier) : 4 * (1 / 3) * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 75 := by ring
  have h3 (p : M.Carrier) : 1 * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 100 := by ring
  have h := exists_fin_packet_family_curvatureScale g hfin S
    (c := 1 / 100) (a := 1 / 3) (C := 1) (by norm_num) (by norm_num) zero_le_one
    (by norm_num) (by norm_num) center plateau domain (by
      intro p hp
      rw [h2, h3]
      exact hpacket p hp)
  have hD : (3 : ℝ) * 1 + 2 * (1 / 3) = 11 / 3 := by norm_num
  have hq : ((11 : ℝ) / 3)⁻¹ = 3 / 11 := by norm_num
  simp only [h1, hD, hq, finrank_euclideanSpace, Fintype.card_fin] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
