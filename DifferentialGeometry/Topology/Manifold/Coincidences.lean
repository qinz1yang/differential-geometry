import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Compactness.Compact
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem eventually_eq_of_hasFDerivWithinAt_injective
    {f : E → F} {K : Set E} {x : E} {L : E →L[ℝ] F}
    (hf : HasFDerivWithinAt f L K x) (hL : Function.Injective L) :
    ∀ᶠ y in 𝓝[K] x, f y = f x → y = x := by
  obtain ⟨C, _, hC⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hne : ∀ᶠ y in 𝓝 x, y ∈ K \ {x} → f y ≠ f x :=
    eventually_nhdsWithin_iff.mp (hf.eventually_ne (c := f x) ⟨C, hC⟩)
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyK heq
  by_contra hyx
  exact hy ⟨hyK, hyx⟩ heq

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

private theorem eventually_eq_of_hasMFDerivWithinAt_sub_injective
    {f g : Q → M} {K : Set Q} {x : Q} {L R : E →L[ℝ] F}
    (hf : HasMFDerivWithinAt I J f K x L)
    (hg : HasMFDerivWithinAt I J g K x R)
    (hfg : f x = g x) (hLR : Function.Injective (L - R)) :
    ∀ᶠ y in 𝓝[K] x, f y = g y → y = x := by
  let c := extChartAt J (f x)
  let d := extChartAt I x
  have hf' : HasFDerivWithinAt (fun z => c (f (d.symm z))) L
      (d.symm ⁻¹' K ∩ range I) (d x) := by
    simpa only [writtenInExtChartAt, Function.comp_def, c, d] using! hf.2
  have hg' : HasFDerivWithinAt (fun z => c (g (d.symm z))) R
      (d.symm ⁻¹' K ∩ range I) (d x) := by
    simpa only [writtenInExtChartAt, Function.comp_def, c, d, hfg] using! hg.2
  have h := eventually_eq_of_hasFDerivWithinAt_injective (hf'.sub hg') hLR
  have ht : Tendsto d (𝓝[K] x) (𝓝[d.symm ⁻¹' K ∩ range I] d x) := by
    change map (extChartAt I x) (𝓝[K] x) ≤ _
    rw [map_extChartAt_nhdsWithin]
  filter_upwards [ht.eventually h, extChartAt_source_mem_nhdsWithin (I := I) (s := K) x]
    with y hy hys heq
  apply (extChartAt I x).injOn hys (mem_extChartAt_source x)
  apply hy
  simp only [Pi.sub_apply, d, (extChartAt I x).left_inv hys, extChartAt_to_inv,
    heq, hfg, sub_self]

theorem finite_coincidences_of_hasMFDerivWithinAt_sub_injective [T2Space M]
    {f g : Q → M} {K : Set Q} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hderiv : ∀ x ∈ K, f x = g x → ∃ L R : E →L[ℝ] F,
      HasMFDerivWithinAt I J f K x L ∧
      HasMFDerivWithinAt I J g K x R ∧ Function.Injective (L - R)) :
    {x | x ∈ K ∧ f x = g x}.Finite := by
  have hcompact : IsCompact {x | x ∈ K ∧ f x = g x} := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hc : IsClosed {x : K | f x = g x} := isClosed_eq hf.domRestrict hg.domRestrict
    have hi := hc.isCompact.image continuous_subtype_val
    convert hi using 1
    ext x
    constructor
    · rintro ⟨hx, hfg⟩
      exact ⟨⟨x, hx⟩, hfg, rfl⟩
    · rintro ⟨y, hfg, rfl⟩
      exact ⟨y.2, hfg⟩
  apply hcompact.finite
  apply IsDiscrete.of_nhdsWithin
  intro x hx
  rw [Filter.le_pure_iff]
  obtain ⟨L, R, hL, hR, hLR⟩ := hderiv x hx.1 hx.2
  have h := eventually_eq_of_hasMFDerivWithinAt_sub_injective hL hR hx.2 hLR
  filter_upwards [h.filter_mono (nhdsWithin_mono x (fun _ h => h.1)),
    self_mem_nhdsWithin] with y hy hyS
  exact hy hyS.2

theorem finite_coincidences_of_mfderivWithin_sub_injective [T2Space M]
    {f g : Q → M} {K : Set Q} (hK : IsCompact K)
    (hf : MDifferentiableOn I J f K)
    (hg : MDifferentiableOn I J g K)
    (htrans : ∀ x ∈ K, f x = g x → Function.Injective
      ((show E →L[ℝ] F from mfderivWithin I J f K x) -
        (show E →L[ℝ] F from mfderivWithin I J g K x))) :
    {x | x ∈ K ∧ f x = g x}.Finite := by
  apply finite_coincidences_of_hasMFDerivWithinAt_sub_injective (I := I) (J := J) hK hf.continuousOn hg.continuousOn
  intro x hx hfg
  exact ⟨_, _, (hf x hx).hasMFDerivWithinAt, (hg x hx).hasMFDerivWithinAt, htrans x hx hfg⟩

theorem finite_coincidences_of_mfderivWithin_sub_surjective [T2Space M]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f g : Q → M} {K : Set Q} (hK : IsCompact K)
    (hf : MDifferentiableOn I J f K)
    (hg : MDifferentiableOn I J g K)
    (htrans : ∀ x ∈ K, f x = g x → Function.Surjective
      ((show E →L[ℝ] F from mfderivWithin I J f K x) -
        (show E →L[ℝ] F from mfderivWithin I J g K x))) :
    {x | x ∈ K ∧ f x = g x}.Finite := by
  apply finite_coincidences_of_mfderivWithin_sub_injective (I := I) hK hf hg
  intro x hx hfg
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (htrans x hx hfg)

end DifferentialGeometry.Topology
end

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ G HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J 1 M]
  [T2Space M]

theorem eventually_injective_mfderiv_sub_at_coincidences_on_isCompact
    {f g : P → Q → M} {K : Set Q} (hK : IsCompact K) {a : P}
    (hf : ∀ x ∈ K, ContMDiffAt (IP.prod I) J 1 (Function.uncurry f) (a, x))
    (hg : ∀ x ∈ K, ContMDiffAt (IP.prod I) J 1 (Function.uncurry g) (a, x))
    (hreg : ∀ x ∈ K, f a x = g a x → Function.Injective
      ((show E →L[ℝ] F from mfderiv I J (f a) x) - (show E →L[ℝ] F from mfderiv I J (g a) x))) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ K, f b x = g b x → Function.Injective
      ((show E →L[ℝ] F from mfderiv I J (f b) x) - (show E →L[ℝ] F from mfderiv I J (g b) x)) := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  by_cases heq : f a x = g a x
  · let A : P × Q → E →L[ℝ] F :=
      inTangentCoordinates I J Prod.snd (fun p : P × Q => f p.1 p.2)
        (fun p => mfderiv I J (f p.1) p.2) (a, x)
    let B : P × Q → E →L[ℝ] F :=
      inTangentCoordinates I J Prod.snd (fun p : P × Q => g p.1 p.2)
        (fun p => mfderiv I J (g p.1) p.2) (a, x)
    have hA : ContinuousAt A (a, x) := by
      have hbase : ContMDiffAt ((IP.prod I).prod I) J 1
          (fun q : (P × Q) × Q => f q.1.1 q.2) ((a, x), x) :=
        (hf x hx).comp ((a, x), x) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
      exact (hbase.mfderiv (fun p : P × Q => f p.1) Prod.snd
        contMDiffAt_snd (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousAt
    have hB : ContinuousAt B (a, x) := by
      have hbase : ContMDiffAt ((IP.prod I).prod I) J 1
          (fun q : (P × Q) × Q => g q.1.1 q.2) ((a, x), x) :=
        (hg x hx).comp ((a, x), x) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
      exact (hbase.mfderiv (fun p : P × Q => g p.1) Prod.snd
        contMDiffAt_snd (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousAt
    have hA0 : A (a, x) = mfderiv I J (f a) x := by
      dsimp only [A]
      erw [inTangentCoordinates_eq_mfderiv_comp (f := Prod.snd)
        (g := fun p : P × Q => f p.1 p.2) (x₀ := (a, x)) (x := (a, x))
        (mem_chart_source H x) (mem_chart_source H' (f a x))]
      simp only [mfderiv_extChartAt_self, mfderivWithin_range_extChartAt_symm]
      ext v
      rfl
    have hB0 : B (a, x) = mfderiv I J (g a) x := by
      dsimp only [B]
      erw [inTangentCoordinates_eq_mfderiv_comp (f := Prod.snd)
        (g := fun p : P × Q => g p.1 p.2) (x₀ := (a, x)) (x := (a, x))
        (mem_chart_source H x) (mem_chart_source H' (g a x))]
      simp only [mfderiv_extChartAt_self, mfderivWithin_range_extChartAt_symm]
      ext v
      rfl
    have hAB : ∀ᶠ p : P × Q in 𝓝 (a, x), Function.Injective (A p - B p) := by
      apply (hA.sub hB).preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds ?_)
      change Function.Injective (A (a, x) - B (a, x))
      rw [hA0, hB0]
      exact hreg x hx heq
    have hsource : ∀ᶠ p : P × Q in 𝓝 (a, x), p.2 ∈ (chartAt H x).source :=
      continuous_snd.continuousAt.eventually
        ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
    have htarget : ∀ᶠ p : P × Q in 𝓝 (a, x), f p.1 p.2 ∈ (chartAt H' (f a x)).source :=
      (hf x hx).continuousAt.eventually
        ((chartAt H' (f a x)).open_source.mem_nhds (mem_chart_source H' (f a x)))
    filter_upwards [hAB, hsource, htarget] with p hp hps hpt hpeq
    have hBs : g p.1 p.2 ∈ (chartAt H' (g a x)).source := by rwa [← heq, ← hpeq]
    have hident : A p - B p =
        (mfderiv J 𝓘(ℝ, F) (extChartAt J (f a x)) (f p.1 p.2)).comp
          (((show E →L[ℝ] F from mfderiv I J (f p.1) p.2) - (show E →L[ℝ] F from mfderiv I J (g p.1) p.2)).comp
            (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
              (extChartAt I x p.2))) := by
      dsimp only [A, B]
      erw [inTangentCoordinates_eq_mfderiv_comp (f := Prod.snd)
        (g := fun p : P × Q => f p.1 p.2) (x₀ := (a, x)) (x := p) hps hpt,
        inTangentCoordinates_eq_mfderiv_comp (f := Prod.snd)
        (g := fun p : P × Q => g p.1 p.2) (x₀ := (a, x)) (x := p) hps hBs]
      rw [← heq, ← hpeq]
      ext v
      change _ - _ = (mfderiv J 𝓘(ℝ, F) (extChartAt J (f a x)) (f p.1 p.2)) (_ - _)
      exact (map_sub (mfderiv J 𝓘(ℝ, F) (extChartAt J (f a x)) (f p.1 p.2)) _ _).symm
    rw [hident] at hp
    have hsur := (isInvertible_mfderivWithin_extChartAt_symm
      ((extChartAt I x).map_source (by simpa only [extChartAt_source] using hps))).surjective
    have hcomp : Function.Injective (fun v : E =>
        (mfderiv J 𝓘(ℝ, F) (extChartAt J (f a x)) (f p.1 p.2))
          (((show E →L[ℝ] F from mfderiv I J (f p.1) p.2) -
            (show E →L[ℝ] F from mfderiv I J (g p.1) p.2)) v)) :=
      hp.of_comp_right (g := (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm
        (range I) (extChartAt I x p.2))) hsur
    exact Function.Injective.of_comp
      (f := mfderiv J 𝓘(ℝ, F) (extChartAt J (f a x)) (f p.1 p.2))
      (g := (show E →L[ℝ] F from mfderiv I J (f p.1) p.2) -
        (show E →L[ℝ] F from mfderiv I J (g p.1) p.2)) hcomp
  · filter_upwards [((hf x hx).continuousAt.prodMk (hg x hx).continuousAt).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds heq)] with p hp hpeq
    exact (hp hpeq).elim

theorem eventually_surjective_mfderiv_sub_at_coincidences_on_isCompact
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f g : P → Q → M} {K : Set Q} (hK : IsCompact K) {a : P}
    (hf : ∀ x ∈ K, ContMDiffAt (IP.prod I) J 1 (Function.uncurry f) (a, x))
    (hg : ∀ x ∈ K, ContMDiffAt (IP.prod I) J 1 (Function.uncurry g) (a, x))
    (hreg : ∀ x ∈ K, f a x = g a x → Function.Surjective
      ((show E →L[ℝ] F from mfderiv I J (f a) x) - (show E →L[ℝ] F from mfderiv I J (g a) x))) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ K, f b x = g b x → Function.Surjective
      ((show E →L[ℝ] F from mfderiv I J (f b) x) - (show E →L[ℝ] F from mfderiv I J (g b) x)) := by
  have h := eventually_injective_mfderiv_sub_at_coincidences_on_isCompact hK hf hg
    (fun x hx heq => (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (hreg x hx heq))
  filter_upwards [h] with b hb x hx heq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hb x hx heq)

end DifferentialGeometry.Topology
end

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

variable {E F EQ H HQ M Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {IQ : ModelWithCorners ℝ EQ HQ}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace Q] [ChartedSpace HQ Q] {n : ℕ∞ω}

theorem surjective_mfderiv_coincidence_iff_in_chart
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : n ≠ 0)
    {g₁ g₂ : Q → M} {q : Q}
    (hg₁ : MDifferentiableAt IQ I g₁ q) (hg₂ : MDifferentiableAt IQ I g₂ q)
    (hq : g₁ q = g₂ q) (hchart : g₁ q ∈ e.source) :
    Function.Surjective (mfderiv IQ 𝓘(ℝ, F) (fun z => e (g₁ z) - e (g₂ z)) q) ↔
      Function.Surjective ((show EQ →L[ℝ] E from mfderiv IQ I g₁ q) -
        (show EQ →L[ℝ] E from mfderiv IQ I g₂ q)) := by
  let A : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) e (g₁ q)
  let B₁ : EQ →L[ℝ] E := mfderiv IQ I g₁ q
  let B₂ : EQ →L[ℝ] E := mfderiv IQ I g₂ q
  have he₁ := e.mdifferentiableAt hn hchart
  have he₂ := e.mdifferentiableAt hn (hq ▸ hchart)
  let C₁ : EQ →L[ℝ] F := mfderiv IQ 𝓘(ℝ, F) (e ∘ g₁) q
  let C₂ : EQ →L[ℝ] F := mfderiv IQ 𝓘(ℝ, F) (e ∘ g₂) q
  have hd₁ : C₁ = A.comp B₁ := mfderiv_comp q he₁ hg₁
  have he₂m : (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) e (g₂ q)) = A := by
    rw [← hq]
  have hd₂ : C₂ = A.comp B₂ := by
    calc
      C₂ = (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) e (g₂ q)).comp B₂ :=
        mfderiv_comp q he₂ hg₂
      _ = A.comp B₂ := by rw [he₂m]
  let C : EQ →L[ℝ] F := mfderiv IQ 𝓘(ℝ, F) (fun z => e (g₁ z) - e (g₂ z)) q
  have hsub : C = C₁ - C₂ :=
    mfderiv_sub (he₁.comp q hg₁) (he₂.comp q hg₂)
  have hd : C = A.comp (B₁ - B₂) := by
    rw [hsub, hd₁, hd₂, ContinuousLinearMap.comp_sub]
  have hA : A.IsInvertible :=
    DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph e hn hchart
  change Function.Surjective C ↔ Function.Surjective (B₁ - B₂)
  rw [hd]
  constructor
  · intro hsurj y
    obtain ⟨x, hx⟩ := hsurj (A y)
    exact ⟨x, hA.injective hx⟩
  · intro hsurj
    exact hA.surjective.comp hsurj

end DifferentialGeometry.Manifold
end
