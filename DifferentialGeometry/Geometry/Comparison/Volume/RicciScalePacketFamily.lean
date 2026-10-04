import DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicityFamily
import DifferentialGeometry.Geometry.Metric.LipschitzScalePacketFamily

/-!
# Finite packet families from pointwise packets (LC87 producer piece P1, Riemannian form)

Blueprint rows LC87 (`def:collapse-local-export`) and LC86, master207A.  On a compact Riemannian
manifold with a positive `Λ`-Lipschitz scale `ρ`, `Λ a ≤ 1/2`, `Λ C ≤ 1/4` and a common normalized
lower Ricci bound on the enlarged comparison balls about the points of a stratum `S`: if EVERY point
`p ∈ S` carries a packet (of an arbitrary type `Pk`) centred at `p` whose plateau contains
`B(p, 4 a ρ(p))` and whose domain lies in `B(p, C ρ(p))`, then a finite family `F : Fin n → Pk` of
such packets has distinct centres in `S`, pairwise disjoint selection balls `B(·, a ρ)`, plateaus
covering `S`, and domain multiplicity at most `V_{-q²}(3C + 2a) / V_{-q²}(a)`: the cover and
overlap fields of LC87 for one family.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompactSpace M]

open _root_.Metric DifferentialGeometry.Integral.Measure

/-- LC87 producer piece P1: finite packet family with cover and multiplicity fields from pointwise
packets, by the LC86 maximal selection. -/
theorem exists_fin_packet_family_of_ricci_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (S : Set M) {ρ : M → ℝ} {Λ : NNReal} {a C q : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (ha : 0 < a) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hsmall : (Λ : ℝ) * a ≤ 1 / 2) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (ball p ((3 * C + 2 * a) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2))))
    {Pk : Type*} (center : Pk → M) (plateau domain : Pk → Set M)
    (hpacket : ∀ p ∈ S, ∃ P : Pk, center P = p ∧ ball p (4 * a * ρ p) ⊆ plateau P ∧
      domain P ⊆ ball p (C * ρ p)) :
    ∃ (n : ℕ) (F : Fin n → Pk), (∀ k, center (F k) ∈ S) ∧
      Function.Injective (fun k => center (F k)) ∧
      Pairwise (fun k l => Disjoint (ball (center (F k)) (a * ρ (center (F k))))
        (ball (center (F l)) (a * ρ (center (F l))))) ∧
      S ⊆ ⋃ k, plateau (F k) ∧
      ∀ x : M, (({k | x ∈ domain (F k)} : Set (Fin n)).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p₀, hp₀⟩
  · subst hS
    refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      empty_subset _, fun x => ?_⟩
    rw [show ({k | x ∈ domain (Fin.elim0 k)} : Set (Fin 0)) = ∅ from
      eq_empty_of_forall_notMem fun k => k.elim0, ncard_empty, Nat.cast_zero]
    have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
      modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
    exact div_nonneg (hm _ (by linarith)).le (hm a ha).le
  have : Nonempty Pk := ⟨(hpacket p₀ hp₀).choose⟩
  choose! pk hpk using hpacket
  obtain ⟨⟨J, hJ⟩, hall⟩ :=
    maximal_scale_selection_of_ricci_bound g hEnorm S hρ hρpos ha hC hq hsmall hoverlap hRic
  obtain ⟨hJfin, hcover, hmult⟩ := hall J hJ
  have hJS : J ⊆ S := hJ.1.1
  obtain ⟨n, F, hFJ, hinj, hdisj, hcov, hm⟩ :=
    GC.MetricGeometry.exists_fin_packet_family_of_selection center plateau domain pk hJfin
      (fun i hi => (hpk i (hJS hi)).1) hJ.1.2 hcover
      (fun i hi => (hpk i (hJS hi)).2.1) (fun i hi => (hpk i (hJS hi)).2.2) hmult
  exact ⟨n, F, fun k => hJS (hFJ k), hinj, hdisj, hcov, hm⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
