import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import Mathlib

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open Set Filter
open scoped BigOperators Topology NNReal Manifold ContDiff

theorem frameODE_linear_solution
    {T : ℝ} (hT : 0 < T)
    (R : ℝ → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ l k : Fin 3, |R t l k| ≤ 1)
    (hRcont : ∀ l k : Fin 3,
      ContinuousOn (fun t : ℝ => R t l k) (Set.Icc 0 T))
    (A₀ : Fin 3 → Fin 3 → ℝ) :
    ∃ iota : ℝ → Fin 3 → Fin 3 → ℝ,
      (∀ a k : Fin 3, iota 0 a k = A₀ a k) ∧
      ContinuousOn (fun q : ℝ × (Fin 3 → Fin 3 → ℝ) => iota q.1)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Fin 3 → Fin 3 → ℝ))) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ a k : Fin 3,
        HasDerivWithinAt (fun s : ℝ => iota s a k)
          (∑ l : Fin 3, R t l k * iota t a l) (Set.Ici 0) t := by
  classical
  let E₀ : Type := Fin 3 → Fin 3 → ℝ
  let K : ℝ≥0 := 3
  let f : ℝ → E₀ → E₀ := fun t A a k => ∑ l : Fin 3, R t l k * A a l
  have hf_lip : ∀ t : ℝ, t ∈ Set.Icc 0 T → LipschitzWith K (f t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun A B => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hlin : f t A - f t B = f t (A - B) := by
      funext a k
      dsimp [f]
      rw [Pi.sub_apply, Pi.sub_apply]
      calc
        (∑ l : Fin 3, R t l k * A a l) - (∑ l : Fin 3, R t l k * B a l) =
            ∑ l : Fin 3, (R t l k * A a l - R t l k * B a l) :=
              (Finset.sum_sub_distrib (fun l : Fin 3 => R t l k * A a l)
                (fun l : Fin 3 => R t l k * B a l)).symm
        _ = ∑ l : Fin 3, R t l k * (A a l - B a l) := by
              refine Finset.sum_congr rfl ?_
              intro l hl
              ring
    rw [hlin]
    have hbound : ‖f t (A - B)‖ ≤ (K : ℝ) * ‖A - B‖ := by
      rw [Pi.norm_def]
      have hsup : (Finset.univ : Finset (Fin 3)).sup
          (fun a : Fin 3 => ‖(f t (A - B)) a‖₊) ≤ (K : ℝ≥0) * ‖A - B‖₊ := by
        refine Finset.sup_le_iff.mpr ?_
        intro a ha
        rw [Pi.nnnorm_def]
        refine Finset.sup_le_iff.mpr ?_
        intro k hk
        have hknn : ‖(f t (A - B)) a k‖₊ ≤ 3 * ‖A - B‖₊ := by
          have hsum : |∑ l : Fin 3, R t l k * (A - B) a l| ≤
              ∑ l : Fin 3, |R t l k| * |(A - B) a l| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun l : Fin 3 => R t l k * (A - B) a l) Finset.univ
          have hterm : ∀ l : Fin 3, |R t l k| * |(A - B) a l| ≤ |(A - B) a l| := by
            intro l
            have hRle : |R t l k| ≤ 1 := hR t ht l k
            exact mul_le_of_le_one_left (abs_nonneg _) hRle
          have hsumle : ∑ l : Fin 3, |R t l k| * |(A - B) a l| ≤
              ∑ l : Fin 3, |(A - B) a l| :=
            Finset.sum_le_sum (fun l hl => hterm l)
          have hentry : ∀ l : Fin 3, |(A - B) a l| ≤ ‖A - B‖₊ := by
            intro l
            have h1 : ‖(A - B) a‖₊ ≤ ‖A - B‖₊ :=
              by
                rw [Pi.nnnorm_def (A - B)]
                exact Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
                  (f := fun b : Fin 3 => ‖(A - B) b‖₊) (Finset.mem_univ a)
            have h2 : ‖(A - B) a l‖₊ ≤ ‖(A - B) a‖₊ := by
              rw [Pi.nnnorm_def ((A - B) a)]
              exact Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
                (f := fun b : Fin 3 => ‖(A - B) a b‖₊) (Finset.mem_univ l)
            exact_mod_cast (le_trans h2 h1)
          have hsumle' : ∑ l : Fin 3, |(A - B) a l| ≤ 3 * ‖A - B‖₊ := by
            have hle : ∀ l : Fin 3, |(A - B) a l| ≤ ‖A - B‖₊ := hentry
            have hsum' : ∑ l : Fin 3, |(A - B) a l| ≤ ∑ l : Fin 3, ‖A - B‖₊ :=
              Finset.sum_le_sum (fun l hl => hle l)
            have hsumv : ∑ l : Fin 3, ‖A - B‖₊ = 3 * ‖A - B‖₊ := by
              rw [Finset.sum_const]
              norm_num
            rw [hsumv] at hsum'
            exact hsum'
          have hmain : |∑ l : Fin 3, R t l k * (A - B) a l| ≤ 3 * ‖A - B‖₊ := by
            exact le_trans hsum (le_trans hsumle hsumle')
          dsimp [f]
          exact_mod_cast hmain
        have hb : (3 : ℝ≥0) * ‖A - B‖₊ ≤ (K : ℝ≥0) * ‖A - B‖₊ := by
          have hK : (3 : ℝ≥0) ≤ (K : ℝ≥0) := by dsimp [K]; rfl
          exact mul_le_mul_of_nonneg_right hK (zero_le _)
        exact le_trans hknn hb
      exact_mod_cast hsup
    simpa [K] using hbound
  have hf_cont : ∀ A : E₀, ContinuousOn (fun t : ℝ => f t A) (Set.Icc 0 T) := by
    intro A
    rw [continuousOn_iff_continuous_restrict]
    have hRr : ∀ l k : Fin 3, Continuous (fun t : Set.Icc 0 T => R t.1 l k) :=
      fun l k => (hRcont l k).restrict
    have hcontA : Continuous (fun t : Set.Icc 0 T => f t.1 A) := by
      rw [continuous_iff_continuousAt]
      intro t
      rw [continuousAt_pi]
      intro a
      rw [continuousAt_pi]
      intro k
      have hsum : ContinuousAt (fun t : Set.Icc 0 T =>
          ∑ l : Fin 3, R t.1 l k * A a l) t := by
        have hterm : ∀ l : Fin 3, Continuous (fun t : Set.Icc 0 T =>
            R t.1 l k * A a l) := by
          intro l
          exact (hRr l k).mul continuous_const
        exact (continuous_finset_sum (Finset.univ) (fun l hl => hterm l)).continuousAt
      simpa [f] using hsum
    simpa [Function.comp_def] using hcontA
  have hf_aff : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ A : E₀,
      ‖f t A‖ ≤ 0 + (K : ℝ) * ‖A‖ := by
    intro t ht A
    have hf0 : f t 0 = 0 := by
      funext a k
      change (∑ l : Fin 3, R t l k * (0 : Fin 3 → Fin 3 → ℝ) a l) =
        (0 : Fin 3 → Fin 3 → ℝ) a k
      simp
    have h := (hf_lip t ht).dist_le_mul A 0
    rw [dist_eq_norm, dist_eq_norm, hf0, sub_zero, sub_zero] at h
    linarith
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound (E := E₀) (f := f) hT
      (by norm_num : 0 ≤ (0 : ℝ)) hf_lip hf_cont hf_aff A₀
  let iota : ℝ → Fin 3 → Fin 3 → ℝ := fun t a k => γ t a k
  refine ⟨iota, ?_, ?_, ?_⟩
  · intro a k
    change γ 0 a k = A₀ a k
    rw [hγ0]
  · have hraw : ContinuousOn (fun q : ℝ × E₀ => γ q.1)
        (Set.Icc 0 T ×ˢ (Set.univ : Set E₀)) := by
      have hfst : ContinuousOn (fun q : ℝ × E₀ => q.1)
          (Set.Icc 0 T ×ˢ (Set.univ : Set E₀)) :=
        continuous_fst.continuousOn
      have hmaps : Set.MapsTo (fun q : ℝ × E₀ => q.1)
          (Set.Icc 0 T ×ˢ (Set.univ : Set E₀)) (Set.Icc 0 T) := by
        intro q hq
        exact hq.1
      exact hγcont.comp hfst hmaps
    exact hraw.congr (fun q hq => rfl)
  · intro t ht a k
    let L : E₀ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3)
        (φ := fun _ : Fin 3 => ℝ) (i := k)).comp
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3)
          (φ := fun _ : Fin 3 => Fin 3 → ℝ) (i := a))
    have hd := hγderiv t ht
    have hcomp : HasDerivWithinAt (fun s : ℝ => L (γ s))
        (L (f t (γ t))) (Set.Ici 0) t :=
      L.hasFDerivAt.comp_hasDerivWithinAt t hd
    have hLγ : ∀ s : ℝ, L (γ s) = γ s a k := by
      intro s
      dsimp [L]
      rfl
    have hLf : L (f t (γ t)) = (f t (γ t)) a k := by
      dsimp [L]
      rfl
    simpa [iota, hLγ, hLf, f] using hcomp

theorem basisOfFinrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) :
    Nonempty (Module.Basis (Fin 3) ℝ E) := by
  classical
  let b := Module.Basis.ofVectorSpace ℝ E
  have hcard : Fintype.card (Module.Basis.ofVectorSpaceIndex ℝ E) = 3 := by
    rw [← hdim]
    exact (Module.finrank_eq_card_basis b).symm
  let e : Module.Basis.ofVectorSpaceIndex ℝ E ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  exact ⟨b.reindex e⟩

def referenceFrameOfBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (b : Module.Basis (Fin 3) ℝ E) :
    Fin 3 → (x : M) → TangentSpace I x :=
  fun a _x => b a

theorem uhlenbeckFrameOn
    {M : Type*} [TopologicalSpace M]
    {T : ℝ} (hT : 0 < T)
    (R : ℝ → M → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ l k : Fin 3, |R t x l k| ≤ 1)
    (hRcont : ∀ l k : Fin 3,
      ContinuousOn (fun q : ℝ × M => R q.1 q.2 l k)
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (A₀ : M → Fin 3 → Fin 3 → ℝ) :
    ∃ iota : ℝ → M → Fin 3 → Fin 3 → ℝ,
      (∀ x : M, ∀ a k : Fin 3, iota 0 x a k = A₀ x a k) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ x : M, ∀ a k : Fin 3,
        HasDerivWithinAt (fun s : ℝ => iota s x a k)
          (∑ l : Fin 3, R t x l k * iota t x a l) (Set.Ici 0) t := by
  classical
  have hRcont_x : ∀ x : M, ∀ l k : Fin 3,
      ContinuousOn (fun t : ℝ => R t x l k) (Set.Icc 0 T) := by
    intro x l k
    have hmap : ContinuousOn (fun t : ℝ => (t, x)) (Set.Icc 0 T) := by fun_prop
    have hsub : Set.MapsTo (fun t : ℝ => (t, x)) (Set.Icc 0 T)
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
      intro t ht
      exact ⟨ht, trivial⟩
    have hc := (hRcont l k).comp hmap hsub
    simpa using hc
  have hEx : ∀ x : M, ∃ gamma : ℝ → Fin 3 → Fin 3 → ℝ,
      (∀ a k : Fin 3, gamma 0 a k = A₀ x a k) ∧
      ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ a k : Fin 3,
        HasDerivWithinAt (fun s : ℝ => gamma s a k)
          (∑ l : Fin 3, R t x l k * gamma t a l) (Set.Ici 0) t := by
    intro x
    rcases frameODE_linear_solution hT (fun t l k => R t x l k)
      (fun t ht l k => hR t ht x l k) (hRcont_x x) (A₀ x) with ⟨γ, h0, _hcont, hderiv⟩
    exact ⟨γ, h0, hderiv⟩
  choose gamma hgamma using hEx
  let iota : ℝ → M → Fin 3 → Fin 3 → ℝ := fun t x a k => gamma x t a k
  refine ⟨iota, ?_, ?_⟩
  · intro x a k
    have h0 := (hgamma x).1 a k
    simpa [iota] using h0
  · intro t ht x a k
    have hd := (hgamma x).2 t ht a k
    simpa [iota] using hd

theorem gramMatrix_posDef_of_basisFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (b : Module.Basis (Fin 3) ℝ E) :
    Matrix.PosDef (fun i j : Fin 3 =>
      g.inner x (referenceFrameOfBasis b i x) (referenceFrameOfBasis b j x)) := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  let v : Fin 3 → TangentSpace I x := fun i => referenceFrameOfBasis b i x
  have hgram_eq : (Matrix.gram ℝ v : Matrix (Fin 3) (Fin 3) ℝ) =
      (fun i j : Fin 3 =>
        g.inner x (referenceFrameOfBasis b i x) (referenceFrameOfBasis b j x)) := by
    ext i j
    simp [Matrix.gram, v, hinner_eq]
  have hli : LinearIndependent ℝ v := by
    simpa [referenceFrameOfBasis] using b.linearIndependent
  have hpd : (Matrix.gram ℝ v).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hli
  simpa [hgram_eq] using hpd

def flowMetricGramMatrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Fin 3 → (x : M) → TangentSpace I x) :
    Real → M → Matrix (Fin 3) (Fin 3) ℝ :=
  fun t x i j => (S.base.metric t).inner x (frame i x) (frame j x)

def flowInverseMetricComponents
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Fin 3 → (x : M) → TangentSpace I x) :
    Real → DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3) :=
  fun t x i j => (flowMetricGramMatrix S frame t x)⁻¹ i j

theorem flowInverseMetricComponents_inverseProperty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (b : Module.Basis (Fin 3) ℝ E) (t : ℝ) (x : M) :
    ∀ i j : Fin 3,
      (∑ k : Fin 3,
        flowInverseMetricComponents S (referenceFrameOfBasis b) t x i k *
          (S.base.metric t).inner x (referenceFrameOfBasis b k x)
            (referenceFrameOfBasis b j x)) =
        if i = j then 1 else 0 := by
  classical
  intro i j
  have hpd : (flowMetricGramMatrix S (referenceFrameOfBasis b) t x).PosDef := by
    simpa [flowMetricGramMatrix] using
      (gramMatrix_posDef_of_basisFrame (S.base.metric t) x b)
  have hu : IsUnit (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) :=
    Matrix.PosDef.isUnit hpd
  haveI : Invertible (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) :=
    hu.invertible
  have hmain := Matrix.inv_mul_cancel_left_of_invertible
    (A := flowMetricGramMatrix S (referenceFrameOfBasis b) t x)
    (B := (1 : Matrix (Fin 3) (Fin 3) ℝ))
  -- hmain : G⁻¹ * (G * 1) = 1
  have hmain' : (flowMetricGramMatrix S (referenceFrameOfBasis b) t x)⁻¹ *
      (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      (flowMetricGramMatrix S (referenceFrameOfBasis b) t x)⁻¹ * M)
      (Matrix.mul_one (flowMetricGramMatrix S (referenceFrameOfBasis b) t x))
    exact h1.symm.trans hmain
  have hrow := congrFun (congrFun hmain' i) j
  -- (G⁻¹ * G) i j = δ_ij — expand the sum
  simpa [Matrix.mul_apply, flowInverseMetricComponents, flowMetricGramMatrix] using hrow

theorem flowInverseMetricComponents_inversePropertyRight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (b : Module.Basis (Fin 3) ℝ E) (t : ℝ) (x : M) :
    ∀ i j : Fin 3,
      (∑ k : Fin 3,
        (S.base.metric t).inner x (referenceFrameOfBasis b i x)
            (referenceFrameOfBasis b k x) *
          flowInverseMetricComponents S (referenceFrameOfBasis b) t x k j) =
        if i = j then 1 else 0 := by
  classical
  intro i j
  have hpd : (flowMetricGramMatrix S (referenceFrameOfBasis b) t x).PosDef := by
    simpa [flowMetricGramMatrix] using
      (gramMatrix_posDef_of_basisFrame (S.base.metric t) x b)
  have hu : IsUnit (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) :=
    Matrix.PosDef.isUnit hpd
  haveI : Invertible (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) :=
    hu.invertible
  have hmain := Matrix.mul_inv_cancel_right_of_invertible
    (A := flowMetricGramMatrix S (referenceFrameOfBasis b) t x)
    (B := (1 : Matrix (Fin 3) (Fin 3) ℝ))
  have hmain' : (flowMetricGramMatrix S (referenceFrameOfBasis b) t x) *
      (flowMetricGramMatrix S (referenceFrameOfBasis b) t x)⁻¹ = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M * (flowMetricGramMatrix S (referenceFrameOfBasis b) t x)⁻¹)
      (one_mul (flowMetricGramMatrix S (referenceFrameOfBasis b) t x))
    exact h1.symm.trans hmain
  have hrow := congrFun (congrFun hmain' i) j
  simpa [Matrix.mul_apply, flowInverseMetricComponents, flowMetricGramMatrix] using hrow

end DifferentialGeometry.PDE.RicciFlow

end
