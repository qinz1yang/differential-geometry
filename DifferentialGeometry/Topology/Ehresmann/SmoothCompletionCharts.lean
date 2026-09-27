import DifferentialGeometry.Topology.Ehresmann.CompletionCharts
import DifferentialGeometry.Geometry.Boundary.InteriorCollar
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology.Manifold

variable {E F H G B M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace M]
  [ChartedSpace H B] [ChartedSpace G M]
  {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}

set_option backward.isDefEq.respectTransparency false in
theorem exists_lower_smooth_completionChart
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hK : IsOpen K) (hKne : K.Nonempty) (hε : 0 < ε) (hgap : a + ε < b)
    (c : PartialDiffeomorph (J.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) M ∞)
    (hsource : c.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε})
    (hzero : ∀ x ∈ K, c (x, 0) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = a + z.2.1 0) :
    ∃ d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b),
      d.source = K ×ˢ Iio ε ∧ d.target = {q | q.1.1 ∈ c.target} ∧
      (∀ z ∈ d.source, (d z).1 = (c (z.1, halfSpaceOneLift z.2), a + z.2)) ∧
      (∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - a)) ∧
      ContMDiffOn (J.prod 𝓘(ℝ)) I ∞
        (d.trans (intervalCompletionInterior hu.continuous a b).symm)
        (d.trans (intervalCompletionInterior hu.continuous a b).symm).source ∧
      ContMDiffOn I (J.prod 𝓘(ℝ)) ∞
        ((intervalCompletionInterior hu.continuous a b).trans d.symm)
        ((intervalCompletionInterior hu.continuous a b).trans d.symm).source := by
  let T := (Homeomorph.refl B).prodCongr halfSpaceOneHomeomorph
  let k := T.symm.transOpenPartialHomeomorph c.toOpenPartialHomeomorph
  have hk : k.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε} := by
    change T.symm ⁻¹' c.source = _
    rw [hsource]
    rfl
  have hkz : ∀ x ∈ K, k (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x := by
    intro x hx
    change c (x, 0) = i x
    exact hzero x hx
  have hkh : ∀ z ∈ k.source, u (k z) = a + z.2.1 := by
    intro z hz
    exact hheight (T.symm z) hz
  obtain ⟨d, hdS, hdT, hdf, hdi⟩ :=
    exists_lower_completionChart hK hKne hε hgap k hk hkz hkh
  have hdf' : ∀ z ∈ d.source,
      (d z).1 = (c (z.1, halfSpaceOneLift z.2), a + z.2) := by
    intro z hz
    rw [hdf z hz, halfSpaceOneLift_eq]
    rfl
  have hdi' : ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - a) := hdi
  refine ⟨d, hdS, hdT, hdf', hdi', ?_, ?_⟩
  · let S := (d.trans (intervalCompletionInterior hu.continuous a b).symm).source
    have htime : ∀ z ∈ S, 0 < z.2 := by
      intro z hz
      have hh : a < (d z).1.2 := hz.2.1
      rw [hdf' z hz.1] at hh
      linarith
    have hpair : ContMDiffOn (J.prod 𝓘(ℝ)) (J.prod (𝓡∂ 1)) ∞
        (fun z : B × ℝ ↦ (z.1, halfSpaceOneLift z.2)) S :=
      contMDiffOn_fst.prodMk (contMDiffOn_halfSpaceOneLift.comp contMDiffOn_snd
        (fun z hz ↦ (htime z hz).le))
    have hmap : MapsTo (fun z : B × ℝ ↦ (z.1, halfSpaceOneLift z.2)) S c.source := by
      intro z hz
      have hz' : z ∈ K ×ˢ Iio ε := hdS ▸ hz.1
      rw [hsource]
      exact ⟨hz'.1, by
        change max z.2 0 < ε
        rw [max_eq_left (htime z hz).le]
        exact hz'.2⟩
    apply (c.contMDiffOn.comp hpair hmap).congr
    intro z hz
    exact congrArg (fun p : M × ℝ ↦ p.1) (hdf' z hz.1)
  · let S := ((intervalCompletionInterior hu.continuous a b).trans d.symm).source
    have hmap : S ⊆ c.target := by
      intro y hy
      have hh : intervalCompletionInclusion u a b y ∈ d.target := hy.2
      rw [hdT] at hh
      exact hh
    have hp : ContMDiffOn I (J.prod 𝓘(ℝ)) ∞
        (fun y : M ↦ ((c.symm y).1, u y - a)) S :=
      (contMDiff_fst.comp_contMDiffOn (c.symm.contMDiffOn.mono hmap)).prodMk
        (hu.contMDiffOn.sub contMDiffOn_const)
    apply hp.congr
    intro y hy
    exact hdi' _ hy.2

set_option backward.isDefEq.respectTransparency false in
theorem exists_upper_smooth_completionChart
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hK : IsOpen K) (hKne : K.Nonempty) (hε : 0 < ε) (hgap : a + ε < b)
    (c : PartialDiffeomorph (J.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) M ∞)
    (hsource : c.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε})
    (hzero : ∀ x ∈ K, c (x, 0) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = b - z.2.1 0) :
    ∃ d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b),
      d.source = K ×ˢ Ioi (-ε) ∧ d.target = {q | q.1.1 ∈ c.target} ∧
      (∀ z ∈ d.source, (d z).1 = (c (z.1, halfSpaceOneLift (-z.2)), b + z.2)) ∧
      (∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - b)) ∧
      ContMDiffOn (J.prod 𝓘(ℝ)) I ∞
        (d.trans (intervalCompletionInterior hu.continuous a b).symm)
        (d.trans (intervalCompletionInterior hu.continuous a b).symm).source ∧
      ContMDiffOn I (J.prod 𝓘(ℝ)) ∞
        ((intervalCompletionInterior hu.continuous a b).trans d.symm)
        ((intervalCompletionInterior hu.continuous a b).trans d.symm).source := by
  let T := (Homeomorph.refl B).prodCongr halfSpaceOneHomeomorph
  let k := T.symm.transOpenPartialHomeomorph c.toOpenPartialHomeomorph
  have hk : k.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε} := by
    change T.symm ⁻¹' c.source = _
    rw [hsource]
    rfl
  have hkz : ∀ x ∈ K, k (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x := by
    intro x hx
    change c (x, 0) = i x
    exact hzero x hx
  have hkh : ∀ z ∈ k.source, u (k z) = b - z.2.1 := by
    intro z hz
    exact hheight (T.symm z) hz
  obtain ⟨d, hdS, hdT, hdf, hdi⟩ :=
    exists_upper_completionChart hK hKne hε hgap k hk hkz hkh
  have hdf' : ∀ z ∈ d.source,
      (d z).1 = (c (z.1, halfSpaceOneLift (-z.2)), b + z.2) := by
    intro z hz
    rw [hdf z hz, halfSpaceOneLift_eq]
    rfl
  have hdi' : ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - b) := hdi
  refine ⟨d, hdS, hdT, hdf', hdi', ?_, ?_⟩
  · let S := (d.trans (intervalCompletionInterior hu.continuous a b).symm).source
    have htime : ∀ z ∈ S, z.2 < 0 := by
      intro z hz
      have hh : (d z).1.2 < b := hz.2.2
      rw [hdf' z hz.1] at hh
      linarith
    have hpair : ContMDiffOn (J.prod 𝓘(ℝ)) (J.prod (𝓡∂ 1)) ∞
        (fun z : B × ℝ ↦ (z.1, halfSpaceOneLift (-z.2))) S :=
      contMDiffOn_fst.prodMk (contMDiffOn_halfSpaceOneLift.comp contMDiffOn_snd.neg
        (fun z hz ↦ neg_nonneg.mpr (htime z hz).le))
    have hmap : MapsTo (fun z : B × ℝ ↦ (z.1, halfSpaceOneLift (-z.2))) S c.source := by
      intro z hz
      have hz' : z ∈ K ×ˢ Ioi (-ε) := hdS ▸ hz.1
      rw [hsource]
      exact ⟨hz'.1, by
        change max (-z.2) 0 < ε
        rw [max_eq_left (neg_nonneg.mpr (htime z hz).le)]
        have hh := hz'.2
        change -ε < z.2 at hh
        linarith⟩
    apply (c.contMDiffOn.comp hpair hmap).congr
    intro z hz
    exact congrArg (fun p : M × ℝ ↦ p.1) (hdf' z hz.1)
  · let S := ((intervalCompletionInterior hu.continuous a b).trans d.symm).source
    have hmap : S ⊆ c.target := by
      intro y hy
      have hh : intervalCompletionInclusion u a b y ∈ d.target := hy.2
      rw [hdT] at hh
      exact hh
    have hp : ContMDiffOn I (J.prod 𝓘(ℝ)) ∞
        (fun y : M ↦ ((c.symm y).1, u y - b)) S :=
      (contMDiff_fst.comp_contMDiffOn (c.symm.contMDiffOn.mono hmap)).prodMk
        (hu.contMDiffOn.sub contMDiffOn_const)
    apply hp.congr
    intro y hy
    exact hdi' _ hy.2

end DifferentialGeometry.Topology.Ehresmann
