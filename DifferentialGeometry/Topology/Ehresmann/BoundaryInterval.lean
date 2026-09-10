import DifferentialGeometry.Topology.Ehresmann.CompletionAtlas
import DifferentialGeometry.Topology.Ehresmann.CompletionProper
import DifferentialGeometry.Topology.Ehresmann.SmoothIntervalFlow
import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import DifferentialGeometry.Geometry.Boundary.SmoothFactorization
import Mathlib.Geometry.Manifold.Instances.Icc
import DifferentialGeometry.Geometry.Metric.Construction.Existence

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Geometry.Boundary Poincare.Topology.Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [CompactSpace M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundary_interval_trivialization_by_flow
    {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    let _ : Fact (a < b) := ⟨hab⟩
    ∃ C : ChartedSpace E (IntervalCompletionSpace u a b), let _ := C
      IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b) ∧
      ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
          (IntervalCompletionSpace u a b) (IntervalCompletionSpace u a b) ∞,
        ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
          (fun p : ℝ × IntervalCompletionSpace u a b ↦ D p.1 p.2) ∧
        D 0 = Diffeomorph.refl 𝓘(ℝ, E) _ ∞ ∧
        (∀ s t, (D s).trans (D t) = D (s + t)) ∧
        (∀ s, (D s).symm = D (-s)) ∧
        ∃ Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
            (boundaryLevel u a b hab.ne hu.continuous hboundary × Icc a b) M ∞,
          (∀ p, u (Θ p) = p.2.1) ∧
          (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) ∧
          (∀ p, intervalCompletionInclusion u a b (Θ p) =
            D (p.2.1 - a) (intervalCompletionInclusion u a b p.1.1.1)) ∧
          (∀ y, intervalCompletionInclusion u a b (Θ.symm y).1.1.1 =
            D (a - u y) (intervalCompletionInclusion u a b y)) ∧
          ∀ y, (Θ.symm y).2.1 = u y := by
  let _ : Fact (a < b) := ⟨hab⟩
  obtain ⟨metric⟩ := DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric (I := I) (M := M)
  obtain ⟨C, hm, hi, hj, hf, hr⟩ :=
    exists_smooth_intervalCompletion metric hab hu hreg hboundary ha hb
  let := C
  let := hm
  let := sigmaCompactSpace_intervalCompletionSpace hu.continuous a b
  let Q := IntervalCompletionSpace u a b
  let F := boundaryLevel u a b hab.ne hu.continuous hboundary
  let inc := intervalCompletionInclusion u a b
  let height := intervalCompletionHeight u a b
  have hemb : IsEmbedding inc :=
    (isClosedEmbedding_intervalCompletionInclusion hu.continuous a b).isEmbedding
  have hbound (x : M) : u x ∈ Icc a b :=
    range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self x)
  have hgraph (q : Q) (hq : height q ∈ Icc a b) : inc q.1.1 = q := by
    have hmem : q ∈ range inc := by
      rw [← preimage_Icc_intervalCompletionHeight hbound]
      exact hq
    obtain ⟨x, rfl⟩ := hmem
    rfl
  obtain ⟨D, hD, hD0, hDadd, hDi, hheight⟩ := exists_interval_transport_of_proper
    height hf (isProperMap_intervalCompletionHeight hu.continuous a b) hr hab.le
  have hforHeight (p : F × Icc a b) : height (D (p.2.1 - a) (inc p.1.1.1)) = p.2.1 := by
    have hh := hheight (inc p.1.1.1) (hbound p.1.1.1) p.2.1 p.2.2
    change height (D (p.2.1 - u p.1.1.1) (inc p.1.1.1)) = p.2.1 at hh
    rwa [p.1.2] at hh
  let forward : F × Icc a b → M := fun p ↦ (D (p.2.1 - a) (inc p.1.1.1)).1.1
  have hforInc (p : F × Icc a b) : inc (forward p) = D (p.2.1 - a) (inc p.1.1.1) :=
    hgraph _ (by rw [hforHeight]; exact p.2.2)
  have hforU (p : F × Icc a b) : u (forward p) = p.2.1 :=
    (congrArg height (hforInc p)).trans (hforHeight p)
  let ret : M → M := fun y ↦ (D (a - u y) (inc y)).1.1
  have hretHeight (y : M) : height (D (a - u y) (inc y)) = a :=
    hheight (inc y) (hbound y) a ⟨le_rfl, hab.le⟩
  have hretInc (y : M) : inc (ret y) = D (a - u y) (inc y) :=
    hgraph _ (by rw [hretHeight]; exact ⟨le_rfl, hab.le⟩)
  have hretU (y : M) : u (ret y) = a :=
    (congrArg height (hretInc y)).trans (hretHeight y)
  have hretBoundary (y : M) : I.IsBoundaryPoint (ret y) := by
    apply isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero _ (hreg _)
    exact Eventually.of_forall (fun w ↦ by rw [hretU]; exact (hbound w).1)
  let returnFiber : M → F := fun y ↦ ⟨⟨ret y, hretBoundary y⟩, hretU y⟩
  let inverse : M → F × Icc a b := fun y ↦ (returnFiber y, ⟨u y, hbound y⟩)
  have hcancel (s : ℝ) (q : Q) : D (-s) (D s q) = q := by
    rw [← hDi]
    exact (D s).symm_apply_apply q
  have hleft (p : F × Icc a b) : inverse (forward p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change ret (forward p) = p.1.1.1
      apply hemb.injective
      rw [hretInc, hforU, hforInc, ← neg_sub, hcancel]
    · exact Subtype.ext (hforU p)
  have hright (y : M) : forward (inverse y) = y := by
    apply hemb.injective
    rw [hforInc]
    change D (u y - a) (inc (ret y)) = inc y
    rw [hretInc, ← neg_sub, hcancel]
  have hforward : ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ forward := by
    apply (contMDiff_iff_comp_of_fullRank_embedding hi hemb hj rfl forward).mpr
    have hh : ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞
        (fun p : F × Icc a b ↦ D (p.2.1 - a) (inc p.1.1.1)) :=
      hD.comp ((((contMDiff_subtypeVal_Icc (x := a) (y := b)).comp contMDiff_snd).sub contMDiff_const).prodMk
      (hi.comp ((contMDiff_boundaryLevelInclusion u a b hab.ne hu.continuous hboundary).comp
        contMDiff_fst)))
    convert hh using 1
    exact funext hforInc
  have hret : ContMDiff I I ∞ ret := by
    apply (contMDiff_iff_comp_of_fullRank_embedding hi hemb hj rfl ret).mpr
    have hh : ContMDiff I 𝓘(ℝ, E) ∞ (fun y : M ↦ D (a - u y) (inc y)) :=
      hD.comp ((contMDiff_const.sub hu).prodMk hi)
    convert hh using 1
    exact funext hretInc
  have hreturn : ContMDiff I hI.boundaryI ∞ returnFiber :=
    (contMDiff_boundaryLevelInclusion_comp_iff u a b hab.ne hu.continuous hboundary).mp hret
  have hinverse : ContMDiff I (hI.boundaryI.prod (𝓡∂ 1)) ∞ inverse := by
    apply hreturn.prodMk
    exact contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨hu.continuous.subtype_mk _, hu⟩
  let Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F × Icc a b) M ∞ :=
    { toEquiv := ⟨forward, inverse, hleft, hright⟩
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  refine ⟨C, hm, D, hD, hD0, hDadd, hDi, Θ, hforU, ?_, hforInc, hretInc, fun _ ↦ rfl⟩
  intro x
  apply hemb.injective
  calc
    inc (Θ (x, ⟨a, le_rfl, hab.le⟩)) = D (a - a) (inc x.1.1) := hforInc _
    _ = inc x.1.1 := by rw [sub_self, hD0]; rfl

theorem exists_boundary_interval_trivialization
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    let _ : Fact (a < b) := ⟨hab⟩
    ∃ Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
        (boundaryLevel u a b hab.ne hu.continuous hboundary × Icc a b) M ∞,
      (∀ p, u (Θ p) = p.2.1) ∧ ∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1 := by
  obtain ⟨_, _, _, _, _, _, _, Θ, hh, hz, _⟩ :=
    exists_boundary_interval_trivialization_by_flow hab hu hreg hboundary ha hb
  exact ⟨Θ, hh, hz⟩

end Poincare.Topology.Ehresmann
