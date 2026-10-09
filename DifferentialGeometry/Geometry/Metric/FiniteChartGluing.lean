import DifferentialGeometry.Geometry.Metric.FiniteGluing
import DifferentialGeometry.Geometry.Metric.FiniteCoefficients
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteOrder
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def finiteChartDiffeomorph {n : ℕ∞ω}
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E n) :
    let S : Opens M := ⟨c.source, c.open_source⟩
    let T : Opens E := ⟨c.target, c.open_target⟩
    Diffeomorph I 𝓘(ℝ, E) S T n := by
  let S : Opens M := ⟨c.source, c.open_source⟩
  let T : Opens E := ⟨c.target, c.open_target⟩
  refine {
    toEquiv := c.toPartialEquiv.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff T _).mp
    exact c.contMDiffOn.comp_contMDiff (contMDiff_subtype_val (I := I) (U := S))
      (fun x => x.property)
  · apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff S _).mp
    exact c.symm.contMDiffOn.comp_contMDiff
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := T)) (fun x => x.property)

private theorem mfderiv_finiteChartDiffeomorph
    {n : ℕ∞ω} (c : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0)
    (x : (⟨c.source, c.open_source⟩ : Opens M)) :
    mfderiv I 𝓘(ℝ, E) (finiteChartDiffeomorph c) x =
      mfderiv I 𝓘(ℝ, E) c (x : M) := by
  let S : Opens M := ⟨c.source, c.open_source⟩
  let T : Opens E := ⟨c.target, c.open_target⟩
  let d := finiteChartDiffeomorph c
  have hchain := mfderiv_comp x
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := T) (n := 1)).mdifferentiableAt one_ne_zero)
    (d.contMDiff.mdifferentiableAt hn)
  rw [mfderiv_subtype_val] at hchain
  change mfderiv I 𝓘(ℝ, E) (fun y : S => c (y : M)) x =
    mfderiv I 𝓘(ℝ, E) d x at hchain
  have hc := mfderiv_comp x (c.mdifferentiableAt hn x.property)
    ((contMDiff_subtype_val (I := I) (U := S) (n := 1)).mdifferentiableAt one_ne_zero)
  rw [mfderiv_subtype_val] at hc
  change mfderiv I 𝓘(ℝ, E) (fun y : S => c (y : M)) x =
    mfderiv I 𝓘(ℝ, E) c (x : M) at hc
  exact hchain.symm.trans hc


theorem exists_unique_contMDiffMetric_of_compatible_charts
    [FiniteDimensional ℝ E] (p : ℕ)
    [IsManifold I ((p + 1 : ℕ) : ℕ∞ω) M] {ι : Type*}
    (c : ι → PartialDiffeomorph I 𝓘(ℝ, E) M E ((p + 1 : ℕ) : ℕ∞ω))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hregular : ∀ i, ContDiffOn ℝ (p : ℕ∞ω) (B i) (c i).target)
    (hsymm : ∀ i x, x ∈ (c i).target → ∀ v w, B i x v w = B i x w v)
    (hpos : ∀ i x, x ∈ (c i).target → ∀ v, v ≠ 0 → 0 < B i x v v)
    (hcompat : ∀ i j x, x ∈ (c i).source → x ∈ (c j).source →
      ∀ v w : TangentSpace I x,
        B i (c i x) (mfderiv I 𝓘(ℝ, E) (c i) x v) (mfderiv I 𝓘(ℝ, E) (c i) x w) =
          B j (c j x) (mfderiv I 𝓘(ℝ, E) (c j) x v) (mfderiv I 𝓘(ℝ, E) (c j) x w)) :
    letI : IsManifold I 1 M := IsManifold.of_le (n := ((p + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
    ∃! G : ContMDiffRiemannianMetric I (p : ℕ∞ω) E (TangentSpace I : M → Type _),
      ∀ i x, x ∈ (c i).source → ∀ v w : TangentSpace I x,
        G.inner x v w =
          B i (c i x) (mfderiv I 𝓘(ℝ, E) (c i) x v) (mfderiv I 𝓘(ℝ, E) (c i) x w) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ((p + 1 : ℕ) : ℕ∞ω))
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
  let S : ι → Opens M := fun i => ⟨(c i).source, (c i).open_source⟩
  let T : ι → Opens E := fun i => ⟨(c i).target, (c i).open_target⟩
  have hn : ((p + 1 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hlocal (i : ι) :
      ∃ g : ContMDiffRiemannianMetric I (p : ℕ∞ω) E (TangentSpace I : S i → Type _),
        ∀ (x : S i) (v w : TangentSpace I (x : M)),
          g.inner x v w = B i (c i (x : M))
            (mfderiv I 𝓘(ℝ, E) (c i) (x : M) v)
            (mfderiv I 𝓘(ℝ, E) (c i) (x : M) w) := by
    obtain ⟨gT, hgT⟩ := DifferentialGeometry.Geometry.exists_contMDiffMetric_of_contDiffOn_bilinearField
      (T i) (p : ℕ∞ω) (B i) (hsymm i) (hpos i) (hregular i)
    obtain ⟨gS, hgS⟩ := DifferentialGeometry.Geometry.exists_finite_order_pullback_metric_of_diffeomorph
      p (p + 1) p le_rfl le_rfl gT (finiteChartDiffeomorph (c i))
    refine ⟨gS, ?_⟩
    intro x v w
    have hs := hgS x v w
    have ht := hgT (finiteChartDiffeomorph (c i) x)
      (mfderiv I 𝓘(ℝ, E) (finiteChartDiffeomorph (c i)) x v)
      (mfderiv I 𝓘(ℝ, E) (finiteChartDiffeomorph (c i)) x w)
    have hd := mfderiv_finiteChartDiffeomorph (I := I) (c i) hn x
    exact hs.trans (ht.trans (congrArg₂ (fun u v => B i (c i (x : M)) u v)
      (congrArg (fun L => L v) hd) (congrArg (fun L => L w) hd)))
  choose g hg using hlocal
  have hcoverS : ∀ x : M, ∃ i, x ∈ S i := hcover
  have heq : ∀ (i j : ι) (x : M) (hi : x ∈ S i) (hj : x ∈ S j)
      (v w : TangentSpace I x), (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w := by
    intro i j x hi hj v w
    rw [hg, hg]
    exact hcompat i j x hi hj v w
  obtain ⟨G, hG, huniq⟩ := exists_unique_contMDiffMetric_of_open_cover S g hcoverS heq
  refine ⟨G, ?_, ?_⟩
  · intro i x hx v w
    exact (hG i ⟨x, hx⟩ v w).trans (hg i ⟨x, hx⟩ v w)
  · intro G' hG'
    apply huniq G'
    intro i x v w
    exact (hG' i (x : M) x.property v w).trans (hg i x v w).symm

end DifferentialGeometry.Geometry.Metric
