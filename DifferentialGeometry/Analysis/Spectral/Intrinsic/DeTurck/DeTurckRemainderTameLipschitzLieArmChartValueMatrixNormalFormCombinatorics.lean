import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.RzMaster

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Analysis.Spectral.M0Abstract

abbrev rchB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.rchB n
abbrev p5B {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.p5B n
abbrev nscB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.nscB n
abbrev insertB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.insertB n
abbrev vbB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.vbB n
abbrev amixHalfB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.amixHalfB n
abbrev r4F {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.r4F n
abbrev r4pfB {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.r4pfB n
abbrev t2F {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.t2F n
abbrev tpfF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.tpfF n
abbrev r3B {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.r3B n
abbrev chrCorrF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.chrCorrF n
abbrev wcF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.wcF n
abbrev dvfbF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.dvfbF n
abbrev d0F {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.d0F n
abbrev O0F {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.o0F n
abbrev vfbF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.vfbF n
abbrev covAF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.covAF n
abbrev covWF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.covWF n
abbrev V0F {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.v0F n
abbrev D1RF {n : ℕ} := @DeTurckCoefficients.LieCorr0NF.d1RF n

theorem m0_master {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) *
      ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    V0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j
      + insertB ig dig ga1 ga0 gbg dga1 dga0 f i j
      + vbB ig cg ga1 ga0 f i j
      + (2 : ℝ) * (amixHalfB ig cg ga1 ga0 gbg f i j + amixHalfB ig cg ga1 ga0 gbg f j i)
      + p5B ig ga0 dga0 f i j
    = O0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j
      - (t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j)
      - D1RF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j := by
  exact DeTurckCoefficients.LieCorr0NF.master_nf ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0
    dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s
    hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

end DifferentialGeometry.Analysis.Spectral.M0Abstract
