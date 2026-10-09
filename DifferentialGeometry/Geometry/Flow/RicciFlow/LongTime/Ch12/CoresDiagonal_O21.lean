import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoresAssembly_O21

set_option autoImplicit false

/-! CH12-O21 G2 — diagonal choice of the coverage accuracy (blueprint HPI08 "common accuracy").

`exists_diagonal_accuracy_O21`: from `∀ w > 0, ∃ T, ∀ t ≥ T, C w t` build one antitone accuracy
`β → 0` with `C (β t) t` for all late `t`.  `exists_bufferedCores_of_cover_O21`: the H5 assembly
with the coverage input in its natural HPI06/HPI07 form (`∀ w ∃ T`, no diagonal). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Diagonal accuracy: `β t = w0 / (N t + 1)`, `N t` = the largest `n ≤ ⌈t⌉` whose first `n`
thresholds are `≤ t`. -/
theorem exists_diagonal_accuracy_O21 {w0 : ℝ} (hw0 : 0 < w0) (C : ℝ → ℝ → Prop)
    (hC : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t, T ≤ t → C w t) :
    ∃ (β : ℝ → ℝ) (Tc : ℝ), (∀ t, Tc ≤ t → 0 < β t) ∧ AntitoneOn β (Ici Tc) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧ (∀ t, β t ≤ w0) ∧
      ∀ t, Tc ≤ t → C (β t) t := by
  classical
  choose T hT using fun n : ℕ => hC (w0 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℕ, ∀ t, N t = Nat.findGreatest (fun n => ∀ m ≤ n, T m ≤ t) ⌈t⌉₊ :=
    ⟨_, fun _ => rfl⟩
  have hNmono : Monotone N := fun a b hab => by
    rw [hN, hN]
    exact Nat.findGreatest_mono (fun n hn m hm => (hn m hm).trans hab) (Nat.ceil_mono hab)
  refine ⟨fun t => w0 / ((N t : ℝ) + 1), T 0, fun t _ => by positivity, ?_, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    have h1 : ((N a : ℝ) + 1) ≤ (N b : ℝ) + 1 := by
      have := hNmono hab
      exact_mod_cast Nat.add_le_add_right this 1
    exact div_le_div_of_nonneg_left hw0.le (by positivity) h1
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (w0 / ε)
    refine ⟨max (n : ℝ) (∑ m ∈ Finset.range (n + 1), |T m|), fun t ht => ?_⟩
    have hP : ∀ m ≤ n, T m ≤ t := fun m hm =>
      (le_abs_self _).trans ((Finset.single_le_sum (fun k _ => abs_nonneg (T k))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans ((le_max_right _ _).trans ht))
    have hnb : n ≤ ⌈t⌉₊ := Nat.cast_le.mp (((le_max_left _ _).trans ht).trans (Nat.le_ceil t))
    have hnN : n ≤ N t := by rw [hN]; exact Nat.le_findGreatest hnb hP
    have hnN' : (n : ℝ) ≤ N t := by exact_mod_cast hnN
    have hn' : w0 < n * ε := by rwa [div_lt_iff₀ hε] at hn
    change w0 / ((N t : ℝ) + 1) < ε
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · intro t
    exact div_le_self hw0.le (by linarith [(Nat.cast_nonneg (N t) : (0 : ℝ) ≤ N t)])
  · intro t ht
    have hP0 : ∀ m ≤ 0, T m ≤ t := fun m hm => by rw [Nat.le_zero.mp hm]; exact ht
    have hspec : ∀ m ≤ N t, T m ≤ t := by rw [hN]; exact Nat.findGreatest_spec (P := fun n => ∀ m ≤ n, T m ≤ t) (Nat.zero_le _) hP0
    exact hT (N t) t (hspec _ le_rfl)

/-- **H5 assembly, coverage in HPI06/HPI07 form** (sheet S5 conclusion verbatim).  As
`exists_bufferedCores_of_family_O21`, except that the last clause is
`∃ w0 > 0, ∀ w > 0, ∃ T, ∀ t ≥ T, ∀ w' ∈ [w, w0], w'-thick ⇒ covered by a model ball of radius w'⁻¹`
(the diagonal accuracy is built here). -/
theorem exists_bufferedCores_of_cover_O21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hfam : ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
      (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
      (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
      (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x)) ∧
      (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) ∧
      (∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t, T ≤ t → ∀ (ht0 : 0 < t) (w' : ℝ),
        w ≤ w' → w' ≤ w0 →
          ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
              ENNReal.ofReal r →
            ENNReal.ofReal (w' * r ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
            ∃ (i : Fin count) (hi : start i ≤ t),
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹)) :
    ∃ B : BufferedPersistentCores F K,
      Nonempty (∀ i : Fin B.count, HyperbolicTruncation (B.model i)) := by
  obtain ⟨count, model, start, α, Ω, map, hs0, hα0, hαanti, hαdec, hsmooth, hemb, hball, herr,
    hpatch, hdisj, ⟨w0, hw0, hcov⟩⟩ := hfam
  obtain ⟨β, Tc, hβ0, hβanti, hβdec, -, hβC⟩ := exists_diagonal_accuracy_O21 hw0 _ hcov
  exact exists_bufferedCores_of_family_O21 F K hHG03 ⟨count, model, start, α, Ω, map, hs0, hα0,
    hαanti, hαdec, hsmooth, hemb, hball, herr, hpatch, hdisj, w0, hw0, β, Tc, hβ0, hβanti, hβdec,
    fun t ht0 htc w' hw' hw'0 => hβC t htc ht0 w' hw' hw'0⟩

end GC.LongTime.Ch12
