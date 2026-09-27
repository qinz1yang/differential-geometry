import DifferentialGeometry.Geometry.Metric.Convergence.Window.AllOrders
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Diagonal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.Bounds

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology
open Filter
open DifferentialGeometry.Geometry.Curvature

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [WeaklyLocallyCompactSpace M]

omit [I.Boundaryless] in
theorem exists_dense_ancient_time_seq :
    ∃ e : ℕ → ℝ, (∀ n : ℕ, e n ≤ 0) ∧
      ∀ t : ℝ, t ≤ 0 → ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, |t - e n| < δ := by
  classical
  let X := {t : ℝ // t ≤ 0}
  have hneX : Nonempty X := ⟨⟨0, le_rfl⟩⟩
  let eX : ℕ → X := TopologicalSpace.denseSeq X
  have hdenseX : DenseRange eX := TopologicalSpace.denseRange_denseSeq X
  refine ⟨fun n => (eX n).1, fun n => (eX n).2, ?_⟩
  intro t ht δ hδ
  let tx : X := ⟨t, ht⟩
  obtain ⟨n, hn⟩ := hdenseX.exists_dist_lt tx hδ
  refine ⟨n, ?_⟩
  simpa [tx, eX, X, Subtype.dist_eq, Real.dist_eq] using hn

omit [IsManifold I 2 M] in
theorem exists_ancient_window_subsequence
    (hne : Nonempty M)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (hgLip : ∀ n : ℕ, ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc (-(n : ℝ)) 0 → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
        ∀ a : ℕ, a ≤ p → ∀ x : M, x ∈ K →
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|)
    (hbdd : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ≤ 0 → ∀ q : ℕ,
      ∀ K : Set M, IsCompact K → ∃ C : ℝ, ∀ k : ℕ, ∀ z : M, z ∈ K →
        metricCovDerivNorm (I := I) q (gSeq (ρ k) t) gRef z ≤ C)
    (hlow : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ≤ 0 → ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v ≤ (gSeq (ρ k) t).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ,
      ∃ gInf : ℝ → SmoothRiemannianMetric I M,
        ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
            metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef < ε := by
  classical
  refine exists_diag_subseq
    (fun n φ => ∃ gInf : ℝ → SmoothRiemannianMetric I M,
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
          metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef < ε)
    ?_ ?_ ?_
  · intro n φ hφ
    obtain ⟨e, he, hdense⟩ := denseIccSeq (beta := -(n : ℝ)) (psiT := 0) (by linarith)
    have hgLip' : ∀ K' : Set M, IsCompact K' → ∀ p : ℕ, ∃ L : ℝ, 0 ≤ L ∧
        ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc (-(n : ℝ)) 0 → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
          ∀ a : ℕ, a ≤ p → ∀ x : M, x ∈ K' →
            metricDerivNorm (I := I) a (gSeq (φ k) s) (gSeq (φ k) t) gRef x ≤ L * |s - t| := by
      intro K' hK' p
      obtain ⟨L, hL, hLb⟩ := hgLip n K' hK' p
      exact ⟨L, hL, fun k s hs t ht a ha x hx => hLb (φ k) s hs t ht a ha x hx⟩
    have hbdd' : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
        ∀ q : ℕ, ∀ K' : Set M, IsCompact K' → ∃ C : ℝ, ∀ k : ℕ, ∀ z : M, z ∈ K' →
          metricCovDerivNorm (I := I) q (gSeq ((φ ∘ ρ) k) t) gRef z ≤ C :=
      fun ρ hρ t ht q K' hK' => hbdd (φ ∘ ρ) (hφ.comp hρ) t ht.2 q K' hK'
    have hlow' : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
        ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
          c * gRef.inner x v v ≤ (gSeq ((φ ∘ ρ) k) t).inner x v v :=
      fun ρ hρ t ht => hlow (φ ∘ ρ) (hφ.comp hρ) t ht.2
    obtain ⟨ψ, hψ, gInf, hconv⟩ :=
      exists_metric_subsequence_tendsto_in_derivative_sup_norm_on_compacts_uniformly_on_time_interval
        (I := I) hne (-(n : ℝ)) 0 gRef (fun k => gSeq (φ k)) e he hdense hgLip' hbdd' hlow'
    exact ⟨ψ, hψ, gInf, hconv⟩
  · intro n φ ψ hψ hP
    obtain ⟨gInf, hgInf⟩ := hP
    refine ⟨gInf, fun K hK p ε hε => ?_⟩
    obtain ⟨k0, hk0⟩ := hgInf K hK p ε hε
    exact ⟨k0, fun k hk t ht => hk0 (ψ k) (le_trans hk (hψ.id_le k)) t ht⟩
  · intro n φ m hP
    obtain ⟨gInf, hgInf⟩ := hP
    refine ⟨gInf, fun K hK p ε hε => ?_⟩
    obtain ⟨k0, hk0⟩ := hgInf K hK p ε hε
    refine ⟨k0 + m, fun k hk t ht => ?_⟩
    have hmk : m ≤ k := by omega
    have hval := hk0 (k - m) (by omega) t ht
    simpa only [Nat.sub_add_cancel hmk] using hval

omit [IsManifold I 2 M] in
theorem exists_ancient_locally_uniform_subsequence
    (hne : Nonempty M)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (hgLip : ∀ n : ℕ, ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc (-(n : ℝ)) 0 → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
        ∀ a : ℕ, a ≤ p → ∀ x : M, x ∈ K →
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|)
    (hbdd : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ≤ 0 → ∀ q : ℕ,
      ∀ K : Set M, IsCompact K → ∃ C : ℝ, ∀ k : ℕ, ∀ z : M, z ∈ K →
        metricCovDerivNorm (I := I) q (gSeq (ρ k) t) gRef z ≤ C)
    (hlow : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ t : ℝ, t ≤ 0 → ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v ≤ (gSeq (ρ k) t).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : ℝ → SmoothRiemannianMetric I M,
      ∀ n : ℕ, ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t : ℝ, t ∈ Set.Icc (-(n : ℝ)) 0 →
          metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef < ε := by
  classical
  obtain ⟨φ, hφ, hW⟩ := exists_ancient_window_subsequence (I := I) hne gSeq gRef hgLip hbdd hlow
  choose G hG using hW
  have hAt : ∀ t : ℝ, t ≤ 0 → ∃ g : SmoothRiemannianMetric I M,
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x : M, x ∈ K →
          metricDerivNorm (I := I) a (gSeq (φ k) t) g gRef x < ε := by
    intro t ht
    obtain ⟨n, hn⟩ : ∃ n : ℕ, -t ≤ (n : ℝ) := exists_nat_ge (-t)
    refine ⟨G n t, fun K hK p ε hε => ?_⟩
    obtain ⟨k0, hk0⟩ := hG n K hK p ε hε
    refine ⟨k0, fun k hk a ha x hx => ?_⟩
    have hmem : t ∈ Set.Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
    exact lt_of_le_of_lt
      (derivNorm_le_sup (I := I) (a := a) (p := p) hK ha (gSeq (φ k) t) (G n t) gRef hx)
      (hk0 k hk t hmem)
  let gInf : ℝ → SmoothRiemannianMetric I M := fun t =>
    if ht : t ≤ 0 then Classical.choose (hAt t ht) else gRef
  have hgInf : ∀ (t : ℝ) (ht : t ≤ 0), ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x : M, x ∈ K →
        metricDerivNorm (I := I) a (gSeq (φ k) t) (gInf t) gRef x < ε := by
    intro t ht K hK p ε hε
    have h := Classical.choose_spec (hAt t ht) K hK p ε hε
    simpa only [gInf, dif_pos ht] using h
  have huniq : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (-(n : ℝ)) 0 → G n t = gInf t := by
    intro n t ht
    refine metric_ext_inner (I := I) (G n t) (gInf t) (fun x => ?_)
    refine ContinuousLinearMap.ext (fun v => ?_)
    refine ContinuousLinearMap.ext (fun w => ?_)
    have h1 : Filter.Tendsto (fun k => (gSeq (φ k) t).inner x v w) Filter.atTop
        (nhds ((G n t).inner x v w)) := by
      exact metricCInf_inner (I := I) (fun k => gSeq (φ k) t) (G n t) gRef
        (fun K hK p ε hε => by
          obtain ⟨k0, hk0⟩ := hG n K hK p ε hε
          exact ⟨k0, fun k hk => hk0 k hk t ht⟩) x v w
    have h2 : Filter.Tendsto (fun k => (gSeq (φ k) t).inner x v w) Filter.atTop
        (nhds ((gInf t).inner x v w)) := by
      refine metricCInf_inner (I := I) (fun k => gSeq (φ k) t) (gInf t) gRef ?_ x v w
      intro K hK p ε hε
      obtain ⟨k0, hk0⟩ := hgInf t ht.2 K hK p (ε / 2) (by positivity)
      refine ⟨k0, fun k hk => ?_⟩
      have hb : metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef ≤ ε / 2 :=
        metricDerivNormSupOn_le_of_forall (I := I) K p (gSeq (φ k) t) (gInf t) gRef (ε / 2)
          (by positivity) (fun a ha x' hx' => le_of_lt (hk0 k hk a ha x' hx'))
      linarith
    exact tendsto_nhds_unique h1 h2
  refine ⟨φ, hφ, gInf, fun n K hK p ε hε => ?_⟩
  obtain ⟨k0, hk0⟩ := hG n K hK p ε hε
  exact ⟨k0, fun k hk t ht => by simpa only [huniq n t ht] using hk0 k hk t ht⟩

end CheegerGromovCompactness
end DifferentialGeometry
