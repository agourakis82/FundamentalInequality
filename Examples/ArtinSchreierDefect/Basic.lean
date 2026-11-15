/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreier
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Data.Int.WithZero
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Field data for the Artin–Schreier defect example

The polynomial results (separability, root translates, absence of a root in
`F_p((t))` or its perfect hull), irreducibility, and the resulting degree-`p`
extension are proved for every prime `p`. The original quadratic API is kept as
the special case `p = 2`.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel
open scoped LaurentSeries WithZero ValuativeRel

namespace ArtinSchreier

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

/-- An Artin–Schreier polynomial of prime degree with no root is irreducible. -/
theorem irreducible_of_not_isRoot (a : K)
    (hroot : ∀ x : K, ¬ (polynomial p a).IsRoot x) :
    Irreducible (polynomial p a) := by
  let f := polynomial p a
  have hfmonic : f.Monic := monic p a
  have hf0 : f ≠ 0 := hfmonic.ne_zero
  have hfnonunit : ¬ IsUnit f := by
    apply Polynomial.not_isUnit_of_natDegree_pos
    simp [f, natDegree_polynomial, (Fact.out : p.Prime).pos]
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hfnonunit hf0
  have hgpos : 0 < g.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hg)
  have hnlt : ¬ g.natDegree < p := by
    intro hlt
    let _ : Fact (Irreducible g) := ⟨hg⟩
    let ι : K →+* AdjoinRoot g := AdjoinRoot.of g
    let r : AdjoinRoot g := AdjoinRoot.root g
    let _ : CharP (AdjoinRoot g) p :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective p
    have hgr : (map ι g).IsRoot r := AdjoinRoot.isRoot_root g
    have hfr : (map ι f).IsRoot r := by
      obtain ⟨q, hq⟩ := hgf
      rw [IsRoot] at hgr ⊢
      rw [hq]
      simp only [Polynomial.map_mul, eval_mul, hgr, zero_mul]
    have hmapf : map ι f = polynomial p (ι a) := by
      simp [f, polynomial]
    have hfr' : (polynomial p (ι a)).IsRoot r := by
      rwa [← hmapf]
    have hfsplits : (map ι f).Splits := by
      rw [hmapf]
      exact splits_of_root p (ι a) r hfr'
    have hgsplits : (map ι g).Splits :=
      hfsplits.of_dvd ((Polynomial.map_eq_zero_iff (f := ι) ι.injective).not.mpr hf0)
        ((map_dvd_map' ι).mpr hgf)
    let S : Subfield (AdjoinRoot g) := ι.fieldRange
    have hdiff (x : AdjoinRoot g) (hx : x ∈ (map ι g).roots) : x - r ∈ S := by
      have hxg : (map ι g).IsRoot x :=
        (mem_roots ((Polynomial.map_eq_zero_iff (f := ι) ι.injective).not.mpr hg.ne_zero)).mp hx
      have hxf : (map ι f).IsRoot x := by
        obtain ⟨q, hq⟩ := (map_dvd_map' ι).mpr hgf
        rw [IsRoot] at hxg ⊢
        rw [hq, eval_mul, hxg, zero_mul]
      rw [hmapf] at hxf
      obtain ⟨i, hi⟩ := (isRoot_iff p (ι a) r x hfr').mp hxf
      apply RingHom.mem_range.mpr
      refine ⟨primeCast p (K := K) i, ?_⟩
      rw [hi, add_sub_cancel_left]
      change ι (ZMod.cast i : K) = ZMod.cast i
      rw [← ZMod.intCast_cast i, map_intCast, ZMod.intCast_cast]
    have hdiffsum :
        ((map ι g).roots.map (fun x ↦ x - r)).sum ∈ S :=
      S.multiset_sum_mem _ (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact hdiff x hx)
    have hnext : (map ι g).nextCoeff ∈ S := by
      apply RingHom.mem_range.mpr
      refine ⟨g.nextCoeff, ?_⟩
      exact (nextCoeff_map ι.injective g).symm
    have hlead : (map ι g).leadingCoeff ∈ S := by
      apply RingHom.mem_range.mpr
      refine ⟨g.leadingCoeff, ?_⟩
      exact (leadingCoeff_map ι).symm
    have hlead0 : (map ι g).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr
        ((Polynomial.map_eq_zero_iff (f := ι) ι.injective).not.mpr hg.ne_zero)
    have hsum : (map ι g).roots.sum ∈ S := by
      have hm := S.mul_mem (S.inv_mem (S.neg_mem hlead)) hnext
      have heq := hgsplits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
      have heqsum : (map ι g).roots.sum =
          (-(map ι g).leadingCoeff)⁻¹ * (map ι g).nextCoeff := by
        rw [heq]
        field_simp
      rw [heqsum]
      exact hm
    have hsumdiff :
        ((map ι g).roots.map (fun x ↦ x - r)).sum =
          (map ι g).roots.sum - (map ι g).roots.card • r := by
      rw [Multiset.sum_map_sub]
      simp
    have hcardr : (map ι g).roots.card • r ∈ S := by
      have hm := S.sub_mem hsum hdiffsum
      have heqcard : (map ι g).roots.card • r =
          (map ι g).roots.sum -
            ((map ι g).roots.map (fun x ↦ x - r)).sum := by
        rw [hsumdiff]
        abel
      rw [heqcard]
      exact hm
    have hcard : (map ι g).roots.card = g.natDegree := by
      rw [← hgsplits.natDegree_eq_card_roots, natDegree_map]
    have hnotdvd : ¬ p ∣ g.natDegree :=
      Nat.not_dvd_of_pos_of_lt hgpos hlt
    have hdcast : (g.natDegree : AdjoinRoot g) ≠ 0 :=
      (CharP.cast_eq_zero_iff (AdjoinRoot g) p g.natDegree).not.mpr hnotdvd
    have hcastmem : (g.natDegree : AdjoinRoot g) ∈ S := by
      apply RingHom.mem_range.mpr
      exact ⟨(g.natDegree : K), by simp [ι]⟩
    have hdr : (g.natDegree : AdjoinRoot g) * r ∈ S := by
      rw [← nsmul_eq_mul, ← hcard]
      exact hcardr
    have hrmem : r ∈ S := by
      have hm := S.mul_mem (S.inv_mem hcastmem) hdr
      simpa [hdcast] using hm
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp hrmem
    apply hroot y
    change f.IsRoot y
    rw [IsRoot] at hfr ⊢
    rw [← hy, eval_map, eval₂_at_apply] at hfr
    exact ι.injective (by simpa using hfr)
  have hfg : p ≤ g.natDegree := Nat.le_of_not_gt hnlt
  have hassoc : Associated g f :=
    Polynomial.associated_of_dvd_of_natDegree_le hgf hf0 (by
      rw [natDegree_polynomial p a]
      exact hfg)
  exact hassoc.irreducible hg

end ArtinSchreier

namespace ArtinSchreierDefect

variable (p : ℕ) [Fact p.Prime]

abbrev Base := LaurentSeries (ZMod p)

instance baseCharP : CharP (Base p) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (Base p)).injective p

/-- The perfect hull inside an algebraic closure, not the complete Laurent field itself. -/
abbrev Hull := ↥(perfectClosure (Base p) (AlgebraicClosure (Base p)))

/-- The Laurent monomial `t⁻¹`. -/
def inverseT : Base p := HahnSeries.single (-1) 1

def standardPolynomial : (Hull p)[X] :=
  ArtinSchreier.polynomial p (algebraMap (Base p) (Hull p) (inverseT p))

instance baseValuativeRel : ValuativeRel (Base p) :=
  .ofValuation (Valued.v : Valuation (Base p) ℤᵐ⁰)

theorem inverseT_value :
    (Valued.v : Valuation (Base p) ℤᵐ⁰) (inverseT p) = WithZero.exp (1 : ℤ) := by
  simpa [inverseT] using LaurentSeries.valuation_single_zpow (ZMod p) (-1)

theorem exp_one_not_pth_power (γ : ℤᵐ⁰) : γ ^ p ≠ WithZero.exp (1 : ℤ) := by
  intro h
  have hh := congrArg WithZero.log h
  have hp := (Fact.out : p.Prime).two_le
  have hh' : p * WithZero.log γ = 1 := by
    simpa [WithZero.log_pow] using hh
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hh' with h | h <;> omega

/-- A root would have pole order `1/p`, impossible in the Laurent field. -/
theorem base_no_root (x : Base p) : x ^ p - x ≠ inverseT p := by
  intro h
  let v : Valuation (Base p) ℤᵐ⁰ := Valued.v
  have ha : v (inverseT p) = WithZero.exp (1 : ℤ) := inverseT_value p
  have ha1 : 1 < v (inverseT p) := by
    rw [ha]
    change WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ)
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hx : 1 < v x := by
    by_contra! hx
    have hxx : v (x ^ p) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
    have hh := v.map_sub_le hxx hx
    rw [h] at hh
    exact (not_le_of_gt ha1) hh
  have hlt : v x < v (x ^ p) := by
    rw [map_pow]
    exact lt_self_pow₀ hx (Fact.out : p.Prime).one_lt
  have hh : v x ^ p = WithZero.exp (1 : ℤ) := by
    rw [← map_pow, ← v.map_sub_eq_of_lt_left hlt, h, ha]
  exact exp_one_not_pth_power p (v x) hh

/-- A separable root cannot first appear in a purely inseparable perfect hull. -/
theorem hull_no_root (x : Hull p) : ¬ (standardPolynomial p).IsRoot x := by
  intro hx
  let f := ArtinSchreier.polynomial p (inverseT p)
  have heval : aeval x f = 0 := by
    simpa [f, standardPolynomial, ArtinSchreier.polynomial, IsRoot] using hx
  have hsep : IsSeparable (Base p) x :=
    (ArtinSchreier.separable p (inverseT p)).of_dvd (minpoly.dvd (Base p) x heval)
  obtain ⟨y, hy⟩ := IsPurelyInseparable.inseparable (Base p) x hsep
  apply base_no_root p y
  apply (algebraMap (Base p) (Hull p)).injective
  rw [map_sub, map_pow, hy]
  simpa [f, ArtinSchreier.polynomial, sub_eq_zero] using heval

/-- The standard Artin–Schreier polynomial over the perfect hull is irreducible. -/
theorem standardPolynomial_irreducible : Irreducible (standardPolynomial p) :=
  ArtinSchreier.irreducible_of_not_isRoot p _ (hull_no_root p)

instance standardPolynomialIrreducible : Fact (Irreducible (standardPolynomial p)) :=
  ⟨standardPolynomial_irreducible p⟩

/-- The degree-`p` Artin–Schreier extension of the perfect hull. -/
abbrev ArtinSchreierExtension := AdjoinRoot (standardPolynomial p)

instance extensionFiniteDimensional :
    FiniteDimensional (Hull p) (ArtinSchreierExtension p) :=
  (ArtinSchreier.monic p _).finite_adjoinRoot

/-- The Artin–Schreier extension has degree `p`. -/
theorem extension_degree : Module.finrank (Hull p) (ArtinSchreierExtension p) = p := by
  change Module.finrank (Hull p) ((Hull p)[X] ⧸ Ideal.span {standardPolynomial p}) = p
  rw [finrank_quotient_span_eq_natDegree]
  exact ArtinSchreier.natDegree_polynomial p _

/-- The canonical generator satisfies its Artin–Schreier equation. -/
theorem root_equation :
    AdjoinRoot.root (standardPolynomial p) ^ p -
        AdjoinRoot.root (standardPolynomial p) =
      algebraMap (Hull p) (ArtinSchreierExtension p)
        (algebraMap (Base p) (Hull p) (inverseT p)) := by
  have h := AdjoinRoot.mk_self (f := standardPolynomial p)
  change (AdjoinRoot.mk (standardPolynomial p))
    (X ^ p - X - C (algebraMap (Base p) (Hull p) (inverseT p))) = 0 at h
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

/-- The original irreducibility theorem at `p = 2`. -/
theorem quadratic_irreducible : Irreducible (standardPolynomial 2) :=
  standardPolynomial_irreducible 2

/-- The original quadratic extension. -/
abbrev QuadraticExtension := ArtinSchreierExtension 2

/-- The original degree computation at `p = 2`. -/
theorem quadratic_degree : Module.finrank (Hull 2) QuadraticExtension = 2 :=
  extension_degree 2

/-- The original generator equation at `p = 2`. -/
theorem quadratic_root_equation :
    AdjoinRoot.root (standardPolynomial 2) ^ 2 -
        AdjoinRoot.root (standardPolynomial 2) =
      algebraMap (Hull 2) QuadraticExtension
        (algebraMap (Base 2) (Hull 2) (inverseT 2)) :=
  root_equation 2

end ArtinSchreierDefect
