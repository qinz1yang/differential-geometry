import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction

/-!
# S-HCOMP G1: rel-boundary smooth approximation of a continuous disk with compact range

`hcomp` of `PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_P2A` asks for
spanning-disk competitors in the open (non-compact) target `(U, G)`.  The existing
`exists_smooth_disk_approximation` assumes `[CompactSpace M]`, and
`exists_smooth_disk_approximation_preserving_trace_area` assumes an already Lipschitz competitor.
Here a continuous disk `q : C(closedDisk, M)` in an arbitrary (not necessarily compact) manifold
`M`, whose boundary trace is a smooth loop `γ`, is replaced by a disk with a smooth extension
across the boundary and the *same* trace `γ`, with image inside any prescribed open `W ⊇ range q`.
The range of `q` is compact, so a local embedding with a smooth retraction near it
(`exists_contMDiff_embedding_retraction_near_isCompact`) replaces the global compactness of the
earlier statements; the exact boundary values come from the collar interpolation of
`DiskTraceApproximation`.  Lipschitz continuity for every smooth Riemannian metric is
`SmoothDiskExtension.lipschitz`.

* `exists_contDiff_diskTrace_approx_of_continuous_HC`: the statement in a normed space.
* `exists_smoothDiskExtension_diskTrace_of_continuous_HC`: the manifold statement.
* `spanningDiskCompetitors_nonempty_of_filling_HC`: the non-compact analogue of
  `spanningDiskCompetitors_nonempty_of_filling_P2A`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace GC.LongTime.CuspP1

/-- Smooth approximation of a continuous map on the closed disk with the exact boundary values
of a smooth loop (normed-space target, uniform convergence on the closed disk). -/
theorem exists_contDiff_diskTrace_approx_of_continuous_HC
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : ℂ → F} (hv : Continuous v)
    (γ : freeLoop F) (hγ : ContDiff ℝ ∞ (fun t : ℝ => γ (t : loopCircle)))
    (htr : ∀ θ, v (diskBoundary θ : ℂ) = γ θ) :
    ∃ u : ℕ → ℂ → F, (∀ j, ContDiff ℝ ∞ (u j)) ∧
      (∀ j θ, u j (diskBoundary θ : ℂ) = γ θ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖u j z - v z‖ ≤ ε := by
  obtain ⟨q, hqs, hqtr⟩ := exists_contDiff_diskTrace_extension γ hγ
  have hw (j : ℕ) : ∃ w : ℂ → F, ContDiff ℝ ∞ w ∧
      ∀ z, dist (w z) (v z) < 1 / ((j : ℝ) + 1) := by
    obtain ⟨w, hws, hwv, -⟩ := hv.exists_contDiff_approx (⊤ : ℕ∞)
      (ε := fun _ => 1 / ((j : ℝ) + 1)) continuous_const (fun _ => by positivity)
    exact ⟨w, hws, hwv⟩
  choose w hws hwv using hw
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 4)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδ' (j : ℕ) : δ j < 1 / 2 := by
    dsimp only [δ]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 4) (by norm_num)]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 3)
    simpa only [δ, Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (3 : ℝ) + 1 = 4 by norm_num] using ht
  have hχ (j : ℕ) := isDiskCollarCutoff_diskCollarCutoff (hδ j) (hδ' j).le
  have hwlim : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖w j z - v z‖ ≤ ε := by
    intro ε hε
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hε
    refine ⟨J, fun j hj z _ => ?_⟩
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    rw [← dist_eq_norm]
    exact ((hwv j z).trans_le h1).le.trans hJ.le
  have hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ := hqtr
  have hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ := htr
  refine ⟨diskCollarFamily (fun j => diskCollarCutoff (δ j)) w q, fun j => ?_,
    diskCollarFamily_diskBoundary hχ hqb, ?_⟩
  · exact diskCollarInterpolation_contDiff (hχ j) (hδ' j) (diskCollarCutoff_contDiff _)
      (hws j) hqs.contDiffOn
  · exact tendstoUniformly_diskCollarFamily hv hqs.continuous hvb hqb hwlim hδlim hχ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **G1.**  A continuous disk `q` in a manifold (compact or not) whose trace is a smooth loop `γ`
is replaced by a disk with the same trace, a smooth extension across the boundary, and image in
any open set `W` containing the range of `q`. -/
theorem exists_smoothDiskExtension_diskTrace_of_continuous_HC {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (q : C(closedDisk, M)) (hq : diskTrace q = γ) {W : Set M} (hW : IsOpen W)
    (hqW : range q ⊆ W) :
    ∃ (v : C(closedDisk, M)) (V : ℂ → M),
      SmoothDiskExtension (E := E) v V ∧ diskTrace v = γ ∧ range v ⊆ W := by
  let _ : Nonempty M := ⟨q ⟨0, by simp⟩⟩
  obtain ⟨N, n, e, r, U, hKN, he, -, -, -, hU, heNU, hr, hleftN⟩ :=
    exists_contMDiff_embedding_retraction_near_isCompact (I := 𝓘(ℝ, E))
      (isCompact_range q.continuous) (range_nonempty q)
  have hleft (p : M) (hp : p ∈ range q) : r (e p) = p := hleftN p (hKN hp)
  have hγq (θ : loopCircle) : γ θ = q (diskBoundary θ) :=
    (congrArg (fun η : freeLoop M => η θ) hq).symm
  let γe : freeLoop (EuclideanSpace ℝ (Fin n)) := ⟨e ∘ γ, he.continuous.comp γ.continuous⟩
  have hγe : ContDiff ℝ ∞ (fun t : ℝ => γe (t : loopCircle)) := (he.comp hγ).contDiff
  have hve : Continuous (e ∘ diskExtension q) :=
    he.continuous.comp (q.continuous.comp diskRetraction_lipschitz.continuous)
  have htre : ∀ θ, (e ∘ diskExtension q) (diskBoundary θ : ℂ) = γe θ := by
    intro θ
    change e (diskExtension q (diskBoundary θ : ℂ)) = e (γ θ)
    rw [diskExtension_coe, hγq]
  obtain ⟨u, hus, hutr, happrox⟩ :=
    exists_contDiff_diskTrace_approx_of_continuous_HC hve γe hγe htre
  -- the open set of points of `U` retracting into `W`, and the compact image of `range q`
  have hO : IsOpen (U ∩ r ⁻¹' W) := hr.continuousOn.isOpen_inter_preimage hU hW
  have hS : IsCompact (e '' range q) := (isCompact_range q.continuous).image he.continuous
  have hSO : e '' range q ⊆ U ∩ r ⁻¹' W := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨heNU ⟨p, hKN hp, rfl⟩, by simpa only [mem_preimage, hleft p hp] using hqW hp⟩
  obtain ⟨η, hη, hηO⟩ := hS.exists_cthickening_subset_open hO hSO
  obtain ⟨J, hJ⟩ := happrox η hη
  have hmem (z : ℂ) (hz : ‖z‖ ≤ 1) : u J z ∈ U ∩ r ⁻¹' W := by
    apply hηO
    refine Metric.mem_cthickening_of_dist_le (u J z) ((e ∘ diskExtension q) z) η
      (e '' range q) ⟨diskExtension q z, ⟨diskRetraction z, rfl⟩, rfl⟩ ?_
    rw [dist_eq_norm]
    exact hJ J le_rfl z hz
  have hmem' (z : closedDisk) : u J z ∈ U ∩ r ⁻¹' W :=
    hmem z (by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property)
  have hcont : Continuous (fun z : closedDisk => r (u J z)) :=
    hr.continuousOn.comp_continuous ((hus J).continuous.comp continuous_subtype_val)
      (fun z => (hmem' z).1)
  refine ⟨⟨fun z => r (u J z), hcont⟩, fun z => r (u J z), ⟨fun _ => rfl, u J ⁻¹' (U ∩ r ⁻¹' W),
    hO.preimage (hus J).continuous, fun z hz => hmem z (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz), ?_⟩, ?_, ?_⟩
  · exact hr.comp (hus J).contMDiff.contMDiffOn (fun _ hz => hz.1)
  · ext θ
    change r (u J (diskBoundary θ : ℂ)) = γ θ
    rw [hutr J θ]
    exact hleft _ ⟨diskBoundary θ, (hγq θ).symm⟩
  · rintro _ ⟨z, rfl⟩
    exact (hmem' z).2

/-- Non-compact analogue of `spanningDiskCompetitors_nonempty_of_filling_P2A`: a smooth loop in a
manifold (compact or not) which bounds a continuous disk has a non-empty spanning-disk competitor
class for every smooth Riemannian metric. -/
theorem spanningDiskCompetitors_nonempty_of_filling_HC
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (hfill : ∃ q : C(closedDisk, M), diskTrace q = γ) :
    (spanningDiskCompetitors g γ).Nonempty := by
  obtain ⟨q, hq⟩ := hfill
  obtain ⟨v, V, hV, hvtr, -⟩ := exists_smoothDiskExtension_diskTrace_of_continuous_HC hγ q hq
    isOpen_univ (subset_univ _)
  exact ⟨v, hvtr, hV.lipschitz g⟩

end GC.LongTime.CuspP1
