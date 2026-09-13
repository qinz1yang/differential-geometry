import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ} {N : ℕ}

private theorem not_isOpen_range_int : ¬ IsOpen (Set.range ((↑) : ℤ → ℝ)) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h 0 ⟨0, by simp⟩
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδlt : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmem : δ ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hδpos]
    exact hδε
  obtain ⟨n, hn⟩ := hball hmem
  have h1 : (0 : ℝ) < (n : ℝ) := by rw [hn]; exact hδpos
  have h2 : (n : ℝ) < 1 := by rw [hn]; exact hδlt
  have h1' : (0 : ℤ) < n := by exact_mod_cast h1
  have h2' : n < 1 := by exact_mod_cast h2
  omega

private def wildProductCurve (p q : M) : ProductCurve M where
  map := fun z t => if z = 0 then (p, 0) else (q, 0)
  y := fun _ _ => 0
  degree := 0
  lift_eq := by
    intro x t
    by_cases h : ((x : Surgery.Topology.Circle)) = 0 <;> simp [h]
  increment := by intro x t; simp

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] in
private theorem not_continuous_wild [Nontrivial M] (p q : M) (hpq : p ≠ q) :
    ¬ Continuous (fun z : ℝ => (if ((z : Surgery.Topology.Circle) = 0) then p else q)) := by
  intro hcont
  have hpre_eq : (fun z : ℝ => (if ((z : Surgery.Topology.Circle) = 0) then p else q)) ⁻¹' {q}ᶜ
      = Set.range ((↑) : ℤ → ℝ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro hz
      by_contra hne
      have hc : ((z : Surgery.Topology.Circle)) = 0 := by
        by_contra hc
        exact hz (if_neg hc)
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hc
      exact hne ⟨n, by rw [← hn]; simp⟩
    · rintro ⟨n, rfl⟩
      have hc : (((n : ℝ) : Surgery.Topology.Circle)) = 0 :=
        (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
      rw [if_pos hc]
      exact hpq
  have hopen : IsOpen (Set.range ((↑) : ℤ → ℝ)) := by
    rw [← hpre_eq]
    exact hcont.isOpen_preimage {q}ᶜ isClosed_singleton.isOpen_compl
  exact not_isOpen_range_int hopen

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] in
private theorem wildProductCurve_projection (p q : M) (x a : ℝ) :
    ((wildProductCurve (M := M) p q).map (x : Surgery.Topology.Circle) a).1 =
      (if ((x : Surgery.Topology.Circle) = 0) then p else q) := by
  simp only [wildProductCurve]
  by_cases h : ((x : Surgery.Topology.Circle)) = 0 <;> simp [h]

theorem RampFamilyInput.contMDiffOn_projection_slice
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (L : RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N) B lambda e)
    {c₀ : ProductCurve M} (hsmooth : c₀.SmoothOn (I := I) {a})
    (hramp : c₀.IsRampOn B.family.metric lambda {a}) (c : ProductCurve M) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun z : ℝ => (c.map (z : Surgery.Topology.Circle) a).1) univ := by
  obtain ⟨sol, -, hsol⟩ := L.local_dependence c₀ hsmooth hramp
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p : ℝ × ℝ => (sol c).projection.lift p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc a b) := (hsol c).1.smooth.1
  have hsub : (univ : Set ℝ) ×ˢ ({a} : Set ℝ) ⊆ univ ×ˢ Icc a b :=
    Set.prod_mono Subset.rfl (fun t ht => by
      rw [mem_singleton_iff] at ht
      rw [ht]
      exact ⟨le_rfl, B.lt.le⟩)
  have hrestrict := hsm.mono hsub
  have hz : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => ((z, a) : ℝ × ℝ)) univ := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_id.prodMk contMDiffOn_const
  have hcomp := hrestrict.comp hz (fun z _ => ⟨mem_univ z, mem_singleton a⟩)
  refine hcomp.congr (fun z _ => ?_)
  simp only [Function.comp_apply, ProductCurve.projection, CurveMap.lift]
  rw [(hsol c).2.2 z]

theorem not_nonempty_rampFamilyInput_of_exists_ramp [Nontrivial M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (h₀ : ∃ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} ∧
      c₀.IsRampOn B.family.metric lambda {a}) :
    ¬ Nonempty (RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N)
      B lambda e) := by
  rintro ⟨L⟩
  obtain ⟨c₀, hs, hr⟩ := h₀
  obtain ⟨p, q, hpq⟩ := exists_pair_ne M
  have hslice := RampFamilyInput.contMDiffOn_projection_slice (I := I) (M := M) (D := D)
    (a := a) (b := b) (N := N) B lambda e L hs hr (wildProductCurve p q)
  refine not_continuous_wild p q hpq ?_
  refine (continuousOn_univ.mp hslice.continuousOn).congr (fun z => ?_)
  exact wildProductCurve_projection p q z a

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
