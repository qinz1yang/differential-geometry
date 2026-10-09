import DifferentialGeometry.Topology.Collar.VerticalChart
import DifferentialGeometry.Topology.Morse.LevelSetInclusion

/-!
# Regular levels crossed once by a vertical chart (F-e, E4 for the Morse level structure)

`nonempty_diffeomorph_levelSet_of_vertical_chart`: for a smooth function `f` on a boundaryless
manifold modelled on `MorseModel (m + 1)`, the regular level `f⁻¹(c)` with the regular-level
structure of the Morse library is smoothly diffeomorphic to the compact base `S` (dimension `m`)
of any `C^k` vertical chart `j : S × (a, b) → M` along which `f` strictly increases, whose vertical
lines all meet the level and whose image contains the level.

`mfderiv_ne_zero_of_deriv_vertical_pos`: positivity of the vertical derivative already makes
`f` regular at the points of the chart, so the regularity hypothesis of the Morse library is
available from the chart data (`not_isCriticalPointAt_of_vertical_chart`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S]

/-- A positive vertical derivative forces a nonzero differential. -/
theorem mfderiv_ne_zero_of_deriv_vertical_pos {f : M → ℝ} {j : S × ℝ → M} {p : S × ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (j p))
    (hj : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j p)
    (hpos : 0 < deriv (fun s : ℝ => f (j (p.1, s))) p.2) :
    mfderiv I 𝓘(ℝ, ℝ) f (j p) ≠ 0 := by
  intro h0
  have hcomp := mfderiv_comp p hf hj
  have hval := mfderiv_comp_vertical_eq_deriv hf hj
  rw [hcomp, h0, ContinuousLinearMap.zero_comp] at hval
  rw [← hval] at hpos
  exact lt_irrefl _ hpos

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.Morse

variable {m : ℕ} {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

omit [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [J.Boundaryless]
  [IsManifold J ∞ S] in
/-- Along a `C^k` vertical chart with positive vertical derivative whose image contains the level,
the level is regular. -/
theorem not_isCriticalPointAt_of_vertical_chart {f : M → ℝ} {c : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a b))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a b, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hlevel : ∀ z, f z = c → z ∈ j '' (univ ×ˢ Ioo a b)) :
    ∀ z : M, f z = c → ¬ IsCriticalPointAt I f z := by
  intro z hz hcrit
  obtain ⟨p, hp, rfl⟩ := hlevel z hz
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hjd : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j p :=
    (hj.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).mdifferentiableAt hk0
  exact mfderiv_ne_zero_of_deriv_vertical_pos ((hf (j p)).mdifferentiableAt (by simp)) hjd
    (hvert p.1 p.2 hp.2) hcrit

/-- **E4 for the regular-level structure.** The regular level `f⁻¹(c)` of a smooth function on a
boundaryless manifold modelled on `MorseModel (m + 1)`, with the structure of the Morse library, is
smoothly diffeomorphic to the compact base `S` (`dim S = m`) of a `C^k` vertical chart `j` along
which `f` strictly increases, provided every vertical line meets the level and the level lies in
the image of `S × (a, b)`. -/
theorem nonempty_diffeomorph_levelSet_of_vertical_chart [Nonempty S] [CompactSpace S]
    [T2Space S] (hdim : Module.finrank ℝ F = m) {f : M → ℝ} {c : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hreg : ∀ x : M, f x = c → ¬ IsCriticalPointAt I f x)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a b))
    (hjinj : InjOn j (univ ×ˢ Ioo a b))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a b, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a b, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a b, f (j (x, s)) = c)
    (hlevel : ∀ z, f z = c → z ∈ j '' (univ ×ˢ Ioo a b)) :
    letI := manifoldLevelSetChartedSpace I f c hf hreg
    Nonempty (LevelSetSpace f c ≃ₘ⟮𝓘(ℝ, MorseModel m), J⟯ S) := by
  let _ := manifoldLevelSetChartedSpace I f c hf hreg
  have _ := manifoldLevelSetIsManifold I f c hf hreg
  have hdimL : Module.finrank ℝ (MorseModel m) = Module.finrank ℝ F := by
    rw [Module.finrank_fin_fun, hdim]
  have hdimM : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ (MorseModel (m + 1)) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, hdim, Module.finrank_self]
  exact nonempty_diffeomorph_of_vertical_chart hdimL hdimM
    (contMDiff_levelSetInclusion I f c hf hreg)
    (mfderiv_manifoldLevelSetInclusion_injective I f c hf hreg) Subtype.val_injective
    (fun y => y.2) (fun z hz => ⟨⟨z, hz⟩, rfl⟩)
    (fun z _ => (hf z).mdifferentiableAt (by simp)) hk hj hjinj hjd
    (fun _ _ => BoundarylessManifold.isInteriorPoint) hvert hcross hlevel

end DifferentialGeometry.Topology.Morse
