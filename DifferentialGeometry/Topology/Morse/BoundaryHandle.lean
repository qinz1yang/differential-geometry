import DifferentialGeometry.Topology.Morse.BoundaryModification
import DifferentialGeometry.Topology.Morse.HandleCollar

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

variable {n k : ℕ} (hk : k ≤ n) [NeZero k] [NeZero (n - k)]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless] [IsManifold I ∞ M]

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold closedCellChartedSpace

local notation "Iext" =>
  (ModelWithCorners.prod (ModelWithCorners.prod (𝓡 (k - 1)) (𝓡 (n - k))) 𝓘(ℝ, ℝ))

local notation "Iclosed" =>
  (ModelWithCorners.prod (ModelWithCorners.prod (𝓡 (k - 1))
    (modelWithCornersEuclideanHalfSpace (((n - k) - 1) + 1))) 𝓘(ℝ, ℝ))

private theorem exists_cocore_collar_of_isNondegenerateCriticalPointAt
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt
      (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k) :
    ∃ data : MorseChart n k hk (f p) I f, data.p = p ∧
      ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ r : ℝ, 0 < r ∧
        ∃ hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R,
          Real.sqrt (2 * ε + 2 * r ^ 2) < data.smoothRadius ∧
          2 * (r ^ 2 + 2 * ε) < (data.R / 2) ^ 2 ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
            ∃ Φ : OpenPartialHomeomorph
                ((CellBoundary k × EuclideanSpace ℝ (Fin (n - k))) × ℝ) M,
              ContMDiffOn Iext I ∞ Φ Φ.source ∧
              ContMDiffOn I Iext ∞ Φ.symm Φ.target ∧
              (∀ q, Φ q = data.χ (recombine hk
                (Real.sqrt (2 * ε + r ^ 2 * ‖q.1.2‖ ^ 2 - 2 * q.2) • q.1.1.val)
                (r • q.1.2))) ∧
              (∀ x ∈ Φ.target,
                (Φ.symm x).1.1.val =
                    ‖negPart hk (data.χ.symm x)‖⁻¹ • negPart hk (data.χ.symm x) ∧
                (Φ.symm x).1.2 = r⁻¹ • posPart hk (data.χ.symm x) ∧
                (Φ.symm x).2 = f x - (f p - ε)) ∧
              (∀ q ∈ Φ.source, f (Φ q) = f p - ε + q.2) ∧
              (∀ (q : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
                ((q.1, q.2.val), t) ∈ Φ.source) ∧
              (∀ q : AttachingRegion k (n - k),
                Φ ((q.1, q.2.val), 0) =
                  (cocoreAttachingEmbedding hk (f p) ε r data hε hR.le q).val) ∧
              (let T : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-δ) δ, isOpen_Ioo⟩
               Manifold.IsSmoothEmbedding Iclosed I ∞
                 (fun q : AttachingRegion k (n - k) × T =>
                   Φ ((q.1.1, q.1.2.val), q.2.val))) ∧
              (∀ (δ₁ θ : ℝ), 0 < δ₁ → 0 < θ →
                ∀ (z : AttachingRegion k (n - k)) (s : Set.Ico (0 : ℝ) 1),
                  ‖z.2.val‖ ^ 2 < 1 - δ₁ / r ^ 2 →
                  ‖z.2.val‖ ^ 2 < 1 - θ / r ^ 2 → s.val < δ / (2 * ε + r ^ 2) →
                  let τ := (2 * ε + r ^ 2 * ‖z.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
                  let q : StandardHandle k (n - k) := (Handle.attachingCollar k (n - k)) (z, s)
                  τ ∈ Set.Ioo (-δ) δ ∧ ((z.1, z.2.val), τ) ∈ Φ.source ∧
                    handleRoundEmbedding hk (f p) ε r δ₁ θ data q = Φ ((z.1, z.2.val), τ) ∧
                    Φ.symm (handleRoundEmbedding hk (f p) ε r δ₁ θ data q) = ((z.1, z.2.val), τ) ∧
                    f (handleRoundEmbedding hk (f p) ε r δ₁ θ data q) = f p - ε + τ ∧
                    1 - Real.sqrt (1 - 2 * τ / (2 * ε + r ^ 2 * ‖z.2.val‖ ^ 2)) = s.val) := by
  let data : MorseChart n k hk (f p) I f := morseChart I f hf p (f p) k hk hnd hindex rfl
  have hdata : data.p = p := by
    have hAnd {P Q : Prop} {α : Type} (F : P → Q → α) (h : P ∧ Q) :
        And.rec F h = F h.1 h.2 := by
      cases h
      rfl
    simp only [data, morseChart, hAnd]
  let ρ : ℝ := min data.R data.smoothRadius
  have hρ : 0 < ρ := lt_min data.radius_pos data.smoothRadius_pos
  let ε : ℝ := ρ ^ 2 / 32
  let r : ℝ := ρ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hsqrt : Real.sqrt (2 * ε + 2 * r ^ 2) < ρ := by
    apply (Real.sqrt_lt' hρ).mpr
    dsimp [ε, r]
    nlinarith only [sq_pos_of_pos hρ]
  have hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R :=
    hsqrt.trans_le (min_le_left _ _)
  have hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.smoothRadius :=
    hsqrt.trans_le (min_le_right _ _)
  have hmargin : 2 * (r ^ 2 + 2 * ε) < (data.R / 2) ^ 2 := by
    have hρR : ρ ≤ data.R := min_le_left _ _
    have hs : ρ ^ 2 ≤ data.R ^ 2 := (sq_le_sq₀ hρ.le data.radius_pos.le).mpr hρR
    dsimp only [r, ε]
    nlinarith only [hs, sq_pos_of_pos hρ]
  refine ⟨data, hdata, ε, hε, r, hr, hR, hR', hmargin, ?_⟩
  obtain ⟨δ, hδ, hδε, Φ, hΦ, hi, hformula, hinv, hheight, hwidth, hzero, hemb, hflat⟩ :=
    exists_isSmoothEmbedding_cocore_collar hk (f p) ε r data hr.ne' hε hR hR'
  exact ⟨δ, hδ, hδε, Φ, hΦ, hi, hformula, hinv, hheight, hwidth, hzero, hemb,
    fun δ₁ θ hδ₁ hθ => hflat δ₁ θ hδ₁ hθ hr⟩

end

end DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

namespace DifferentialGeometry.Topology.Morse

open CellAttachment
open DifferentialGeometry.Topology.Handle
open ManifoldCellAttachment

noncomputable section

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold closedCellChartedSpace

theorem exists_boundaryMorsePerturbation_with_cocore_collar_in_interior
    {n : ℕ} (k : Fin (n + 1)) [NeZero k.val]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel (n + 1)) H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [I.Boundaryless] [IsManifold I ∞ M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (hdindex : {i | d i < 0}.ncard = k.val) (b : ContDiffBump (0 : Fin n → ℝ))
    (D : Set M) (hD : ∀ x : U, (x : M) ∈ D ↔ 0 ≤ (c x).val 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (v : ℝ)
    (hchart : ∀ x : U, (x : M) ∈ D →
      f x = v + ((∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0)) :
    let _ : NeZero (n + 1 - k.val) := ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt k.isLt)⟩
    ∃ a₀ > 0, ∀ a ∈ Set.Ioc 0 a₀,
      {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V →
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧ HasCompactSupport (g - f) ∧
        tsupport (g - f) ⊆ U ∧
        (∀ x : U, (x : M) ∈ D → g x = v + boundaryMorsePerturbation d b a (c x)) ∧
        Set.EqOn g f (U : Set M)ᶜ ∧
        (∀ x ∈ D, g x - f x ∈ Set.Icc 0 (2 * a)) ∧
        ∃ p : U, ∃ hpD : (p : M) ∈ interior D,
          (c p).val = Fin.cons (a / 2) 0 ∧
          g p = v + boundaryMorsePerturbation d b a (Fin.cons (a / 2) 0) ∧
          IsNondegenerateCriticalPointAt I g (p : M) ∧
          _root_.sigNeg (chartHessianAt (fun z => g ((extChartAt I (p : M)).symm z))
            (extChartAt I (p : M) (p : M))) = k.val ∧
          (∀ x : U, 0 < (c x).val 0 → (IsCriticalPointAt I g (x : M) ↔ x = p)) ∧
          (∀ x ∈ D, IsCriticalPointAt I g x ↔
            x = (p : M) ∨ (x ∉ (U : Set M) ∧ IsCriticalPointAt I f x)) ∧
          (∃ q : U, (q : M) ∈ frontier D ∧ (c q).val = 0 ∧
            tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ)) (g (q : M))
              (mfderiv I 𝓘(ℝ) g (q : M)
                (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) I c.symm (c q) (Fin.cons 1 0))) = -1) ∧
          let O : TopologicalSpace.Opens M := ⟨interior D ∩ (U : Set M), isOpen_interior.inter U.isOpen⟩
          let pO : O := ⟨p.val, hpD, p.property⟩
          ∃ data : MorseChart (n + 1) k.val k.isLt.le (g p) I (fun x : O => g x),
            data.p = pO ∧
            ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ r : ℝ, 0 < r ∧
              ∃ hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R,
                Real.sqrt (2 * ε + 2 * r ^ 2) < data.smoothRadius ∧
                2 * (r ^ 2 + 2 * ε) < (data.R / 2) ^ 2 ∧
                ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
                  ∃ Φ : OpenPartialHomeomorph
                      ((CellBoundary k.val × EuclideanSpace ℝ (Fin (n + 1 - k.val))) × ℝ) O,
                    ContMDiffOn
                      (((𝓡 (k.val - 1)).prod (𝓡 (n + 1 - k.val))).prod 𝓘(ℝ, ℝ))
                      I ∞ Φ Φ.source ∧
                    ContMDiffOn I
                      (((𝓡 (k.val - 1)).prod (𝓡 (n + 1 - k.val))).prod 𝓘(ℝ, ℝ))
                      ∞ Φ.symm Φ.target ∧
                    (∀ q, Φ q = data.χ (recombine k.isLt.le
                      (Real.sqrt (2 * ε + r ^ 2 * ‖q.1.2‖ ^ 2 - 2 * q.2) • q.1.1.val)
                      (r • q.1.2))) ∧
                    (∀ x ∈ Φ.target,
                      (Φ.symm x).1.1.val =
                          ‖negPart k.isLt.le (data.χ.symm x)‖⁻¹ •
                            negPart k.isLt.le (data.χ.symm x) ∧
                      (Φ.symm x).1.2 = r⁻¹ • posPart k.isLt.le (data.χ.symm x) ∧
                      (Φ.symm x).2 = g x - (g p - ε)) ∧
                    (∀ q ∈ Φ.source, g (Φ q) = g p - ε + q.2) ∧
                    (∀ (q : AttachingRegion k.val (n + 1 - k.val)) (t : ℝ),
                      t ∈ Set.Ioo (-δ) δ → ((q.1, q.2.val), t) ∈ Φ.source) ∧
                    (∀ q : AttachingRegion k.val (n + 1 - k.val),
                      Φ ((q.1, q.2.val), 0) =
                        (cocoreAttachingEmbedding k.isLt.le (g p) ε r data hε hR.le q).val) ∧
                    (let T : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-δ) δ, isOpen_Ioo⟩
                     Manifold.IsSmoothEmbedding
                       (((𝓡 (k.val - 1)).prod
                         (modelWithCornersEuclideanHalfSpace (((n + 1 - k.val) - 1) + 1))).prod
                         𝓘(ℝ, ℝ)) I ∞
                       (fun q : AttachingRegion k.val (n + 1 - k.val) × T =>
                         Φ ((q.1.1, q.1.2.val), q.2.val))) ∧
                    (∀ (δ₁ θ : ℝ), 0 < δ₁ → 0 < θ →
                      ∀ (z : AttachingRegion k.val (n + 1 - k.val)) (s : Set.Ico (0 : ℝ) 1),
                        ‖z.2.val‖ ^ 2 < 1 - δ₁ / r ^ 2 →
                        ‖z.2.val‖ ^ 2 < 1 - θ / r ^ 2 → s.val < δ / (2 * ε + r ^ 2) →
                        let τ := (2 * ε + r ^ 2 * ‖z.2.val‖ ^ 2) * (2 * s.val - s.val ^ 2) / 2
                        let q : StandardHandle k.val (n + 1 - k.val) :=
                          (Handle.attachingCollar k.val (n + 1 - k.val)) (z, s)
                        τ ∈ Set.Ioo (-δ) δ ∧ ((z.1, z.2.val), τ) ∈ Φ.source ∧
                          handleRoundEmbedding k.isLt.le (g p) ε r δ₁ θ data q = Φ ((z.1, z.2.val), τ) ∧
                          Φ.symm (handleRoundEmbedding k.isLt.le (g p) ε r δ₁ θ data q) = ((z.1, z.2.val), τ) ∧
                          g ((handleRoundEmbedding k.isLt.le (g p) ε r δ₁ θ data q : O) : M) = g p - ε + τ ∧
                          1 - Real.sqrt (1 - 2 * τ / (2 * ε + r ^ 2 * ‖z.2.val‖ ^ 2)) = s.val) := by
  let _ : NeZero (n + 1 - k.val) := ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt k.isLt)⟩
  obtain ⟨a₀, ha₀, hconstruction⟩ :=
    exists_boundaryMorsePerturbation_with_criticalPoint_in_chart c d hd b D hD f hf v hchart
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha hbox
  obtain ⟨g, hg, hgs, hgU, hmodel, hout, hbound, p, hpD, hp, hnd, hindex, hunique, hglobal, hboundary⟩ :=
    hconstruction a ha hbox
  have hheight : g p = v + boundaryMorsePerturbation d b a (Fin.cons (a / 2) 0) := by
    rw [hmodel p (interior_subset hpD), hp]
  have hindex' := hindex.trans hdindex
  refine ⟨g, hg, hgs, hgU, hmodel, hout, hbound, p, hpD, hp, hheight,
    hnd, hindex', hunique, hglobal, hboundary, ?_⟩
  let O : TopologicalSpace.Opens M := ⟨interior D ∩ (U : Set M), isOpen_interior.inter U.isOpen⟩
  let pO : O := ⟨p.val, hpD, p.property⟩
  have hgO : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : O => g x) :=
    hg.comp (contMDiff_subtype_val (I := I) (U := O))
  have hndO : IsNondegenerateCriticalPointAt I (fun x : O => g x) pO :=
    (isNondegenerateCriticalPointAt_subtype_iff (I := I) O).mpr hnd
  have hindexO : _root_.sigNeg (chartHessianAt
      (fun z => g (((extChartAt I pO).symm z : O) : M)) (extChartAt I pO pO)) = k.val :=
    (congrArg _root_.sigNeg (chartHessianAt_subtype (I := I) O g pO)).trans hindex'
  exact exists_cocore_collar_of_isNondegenerateCriticalPointAt k.isLt.le I
    (fun x : O => g x) hgO pO hndO hindexO

end

end DifferentialGeometry.Topology.Morse
