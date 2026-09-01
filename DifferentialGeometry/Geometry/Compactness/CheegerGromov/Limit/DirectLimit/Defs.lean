import DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness
import DifferentialGeometry.Topology.Exhaustion

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

abbrev limitPointed
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (ginf : SmoothRiemannianMetric I S.toSeqSystem.Lim) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := S.toSeqSystem.Lim
  basepoint := S.toSeqSystem.incl 0 O₀
  metric := ginf

abbrev limitPointedCoc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  limitPointed S O₀ (S.limitMetric g hg)

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

abbrev factorPointed (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := A k
  basepoint := S.toSeqSystem.F (Nat.zero_le k) O₀
  metric := g k

abbrev factorSeq (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := factorPointed S O₀ g

omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (k : ℕ), SigmaCompactSpace (A k)]
    [∀ (k : ℕ), T2Space (A k)] in
theorem range_exhausts (S : SmoothSeqSystem I A) :
    ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k)) where
  isOpen k := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  mono_step k := S.toSeqSystem.range_incl_mono (Nat.le_succ k)
  subset K hK := by
    obtain ⟨k₀, Kk, _, hKeq⟩ := S.toSeqSystem.isCompact_exists hK
    refine ⟨k₀, fun k hk => ?_⟩
    rw [hKeq]
    exact (Set.image_subset_range _ _).trans (S.toSeqSystem.range_incl_mono hk)

noncomputable def limitCGMapsOf (S : SmoothSeqSystem I A) (O₀ : A 0)
    (gSeq gLim : ∀ k, SmoothRiemannianMetric I (A k)) (hgLim : S.MetricCocycle gLim) :
    PointedRiemannianCGMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ gSeq)
      (L := (limitPointedCoc S O₀ gLim hgLim :
        PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) where
  partialDiffeomorph k := S.inclPartialDiffeo k
  source_exhausts := range_exhausts S
  base_mem k := ⟨S.toSeqSystem.F (Nat.zero_le k) O₀, S.toSeqSystem.incl_comp (Nat.zero_le k) O₀⟩
  basepoint_map k := S.invIncl_incl_le (Nat.zero_le k) O₀

noncomputable def limitCGMaps (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianCGMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ g)
      (L := (limitPointedCoc S O₀ g hg : PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) :=
  limitCGMapsOf S O₀ g g hg

end

end HCGCompactness
end DifferentialGeometry
