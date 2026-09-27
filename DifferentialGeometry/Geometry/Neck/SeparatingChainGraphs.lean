import DifferentialGeometry.Geometry.Neck.SeparatingChainGeometry
import DifferentialGeometry.Geometry.Neck.RecordedCollarGraph

noncomputable section
open Set Topology
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Affine

namespace DifferentialGeometry.Geometry.Neck

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

section Graph

variable {E H W F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric J M} {Cₒ ε : ℝ} {n : ℕ} [NeZero n]

structure separatingNeckChain.collarGraph
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1)) where
  lower : C(S², ℝ)
  upper : C(S², ℝ)
  ordered : ∀ p, lower p < upper p
  lower_mem : ∀ p, (p, (D.alignment i).1 * lower p) ∈ (D.charts i).domain
  upper_mem : ∀ p, (p, (D.alignment i).1 * upper p) ∈ (D.charts i).domain
  lowerFace_image : range (fun p ↦
    ((D.charts i).chart ⟨(p, (D.alignment i).1 * lower p), lower_mem p⟩ : M)) =
      range (D.collar j).lowerFace
  upperFace_image : range (fun p ↦
    ((D.charts i).chart ⟨(p, (D.alignment i).1 * upper p), upper_mem p⟩ : M)) =
      range (D.collar j).upperFace
  band_domain : {x : S² × ℝ |
    lower x.1 ≤ (D.alignment i).1 * x.2 ∧ (D.alignment i).1 * x.2 ≤ upper x.1} ⊆
      (D.charts i).domain
  band_image : (D.charts i).region ((Subtype.val : (D.charts i).domain → S² × ℝ) ⁻¹'
    {x | lower x.1 ≤ (D.alignment i).1 * x.2 ∧ (D.alignment i).1 * x.2 ≤ upper x.1}) =
      range (D.collar j).map

end Graph

theorem exists_uniform_collar_graphs_of_separating_chain (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀
    {E H W F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M],
    ∀ (g : SmoothRiemannianMetric J M) (ε : ℝ), 0 ≤ ε → ε < ε₀ →
    ∀ (n : ℕ) [NeZero n] (D : separatingNeckChain I g Cₒ ε n (W := W)),
    ∀ (j : Fin n) (i : Fin (n + 1)), i = j.castSucc ∨ i = j.succ →
      Nonempty (D.collarGraph j i) := by
  obtain ⟨ε₀, hε₀, hproducer⟩ := exists_uniform_graphs_of_recorded_collar_estimates Cₒ hCₒ
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H W F G M _ _ _ I _ _ _ _ _ _ J _ _ _ _ _ g ε hεnonneg hε n _ D j i hi
  let adj : Fin 2 → Fin (n + 1) := ![j.castSucc, j.succ]
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, adj k = D.origin j := by
    rcases D.origin_adjacent j with hk | hk
    · exact ⟨0, hk.symm⟩
    · exact ⟨1, hk.symm⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin 2, adj q = i := by
    rcases hi with hi | hi
    · exact ⟨0, hi.symm⟩
    · exact ⟨1, hi.symm⟩
  let C : Fin 2 → cylindricalChart J (M := M) := fun t ↦ D.charts (adj t)
  let U : ∀ t, Set (C t).domain := fun t ↦ D.controlledDomain (adj t)
  let τ : Fin 2 → ℝ := fun t ↦ (D.alignment (adj t)).1
  have hτ (t : Fin 2) : τ t = 1 ∨ τ t = -1 :=
    finiteLineAffineAlignment_sign D.sign D.edgeTranslation D.sign_unit (adj t)
  have hcompat : τ 1 = τ 0 * D.sign j :=
    congrArg Prod.fst (finiteLineAffineAlignment_succ D.sign D.edgeTranslation j)
  have hc (x : S² × Icc (D.collar j).lower (D.collar j).upper) :
      (x.1, τ k * (x.2 : ℝ)) ∈ (C k).domain := by
    dsimp only [C, τ]
    rw [hk]
    exact (D.collar j).contained x.1 x.2 x.2.property
  let e : S² × Icc (D.collar j).lower (D.collar j).upper → M := fun x ↦
    (C k).chart ⟨(x.1, τ k * (x.2 : ℝ)), hc x⟩
  have he (x : S² × Icc (D.collar j).lower (D.collar j).upper) :
      e x = (D.collar j).map x := by
    have hmap (u v : Fin (n + 1)) (huv : u = v)
        (hu : (x.1, (D.alignment u).1 * (x.2 : ℝ)) ∈ (D.charts u).domain)
        (hv : (x.1, (D.alignment v).1 * (x.2 : ℝ)) ∈ (D.charts v).domain) :
        ((D.charts u).chart ⟨(x.1, (D.alignment u).1 * (x.2 : ℝ)), hu⟩ : M) =
          ((D.charts v).chart ⟨(x.1, (D.alignment v).1 * (x.2 : ℝ)), hv⟩ : M) := by
      subst v
      rfl
    exact hmap (adj k) (D.origin j) hk (hc x) ((D.collar j).contained x.1 x.2 x.2.property)
  have hboth (t : Fin 2) (x : S² × Icc (D.collar j).lower (D.collar j).upper) :
      e x ∈ (C t).region (U t) := by
    rw [he]
    have h := D.overlap_controlled j (D.collar_overlap j ⟨x, rfl⟩)
    fin_cases t
    · exact h.1
    · exact h.2
  have hvalue (x : S² × Icc (D.collar j).lower (D.collar j).upper) :
      |(C 1).axial (e x) - (D.sign j * (C 0).axial (e x) + D.edgeTranslation j)| ≤
        Cₒ * ε / Real.sqrt (C 0).scale := by
    rw [he]
    exact (D.recorded_collar_errors j ⟨x, rfl⟩).1
  have hgradient (x : S² × Icc (D.collar j).lower (D.collar j).upper) :
      Real.sqrt (g.inner (e x)
        (gradFun g (C 1).axial (e x) - D.sign j • gradFun g (C 0).axial (e x))
        (gradFun g (C 1).axial (e x) - D.sign j • gradFun g (C 0).axial (e x))) ≤ Cₒ * ε := by
    rw [he]
    exact (D.recorded_collar_errors j ⟨x, rfl⟩).2
  obtain ⟨a, b, ha, hb, hab, hma, hmb, hface₀, hface₁, hband, himage⟩ :=
    hproducer J g C U ε hεnonneg hε (fun t ↦ D.metric_close (adj t))
      (D.sign j) (D.edgeTranslation j) (D.sign_unit j) τ hτ hcompat k q
      (D.collar j).lower (D.collar j).upper (D.collar j).width hc hboth hvalue hgradient
  rw [← hq]
  refine ⟨{
    lower := ⟨a, ha⟩
    upper := ⟨b, hb⟩
    ordered := hab
    lower_mem := hma
    upper_mem := hmb
    lowerFace_image := ?_
    upperFace_image := ?_
    band_domain := hband
    band_image := ?_ }⟩
  · exact hface₀.trans (congrArg range (funext (fun p ↦
      he (p, ⟨(D.collar j).lower, le_rfl, by linarith only [(D.collar j).width]⟩))))
  · exact hface₁.trans (congrArg range (funext (fun p ↦
      he (p, ⟨(D.collar j).upper, by linarith only [(D.collar j).width], le_rfl⟩))))
  · exact himage.symm.trans (congrArg range (funext he))

end DifferentialGeometry.Geometry.Neck
