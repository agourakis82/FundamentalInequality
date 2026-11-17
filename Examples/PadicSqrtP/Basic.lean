/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.Bridge.Completeness
public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The quadratic extension `ℚ_p(√p)`

For every prime `p`, this file proves by Eisenstein's criterion that
`X² - p` is irreducible over `ℚ_[p]`, defines its `AdjoinRoot`, and computes
the extension degree.

## References

* [J.-P. Serre, *Local Fields*][serreLocalFields], Chapter II, §2.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace PadicSqrtP

variable (p : ℕ) [Fact p.Prime]

/-- The integral polynomial used for Eisenstein's criterion. -/
def integerPolynomial : (ℤ_[p])[X] := X ^ 2 - C (p : ℤ_[p])

/-- The polynomial `X² - p` over the `p`-adic numbers. -/
def polynomial : (ℚ_[p])[X] := X ^ 2 - C (p : ℚ_[p])

theorem integerPolynomial_monic : (integerPolynomial p).Monic := by
  exact monic_X_pow_sub_C (p : ℤ_[p]) (by norm_num)

theorem integerPolynomial_natDegree : (integerPolynomial p).natDegree = 2 := by
  exact natDegree_X_pow_sub_C (p : ℤ_[p])

/-- `X² - p` is Eisenstein at the maximal ideal `(p)` of `ℤ_[p]`. -/
theorem integerPolynomial_isEisenstein :
    (integerPolynomial p).IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
  apply (integerPolynomial_monic p).isEisensteinAt_of_mem_of_notMem
  · rw [← PadicInt.maximalIdeal_eq_span_p]
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
  · intro n hn
    have hn' : n < 2 := by simpa [integerPolynomial_natDegree] using hn
    interval_cases n <;> simp [integerPolynomial]
  · intro h
    rw [Ideal.span_singleton_pow] at h
    have hp : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ 2} := by
      simpa [integerPolynomial] using h
    have hle := (PadicInt.mem_span_pow_iff_le_valuation (p : ℤ_[p])
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) 2).mp hp
    norm_num at hle

/-- The integral polynomial `X² - p` is irreducible by Eisenstein's criterion. -/
theorem integerPolynomial_irreducible : Irreducible (integerPolynomial p) := by
  apply (integerPolynomial_isEisenstein p).irreducible
  · rw [← PadicInt.maximalIdeal_eq_span_p]
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).isPrime
  · exact (integerPolynomial_monic p).isPrimitive
  · simp [integerPolynomial_natDegree]

theorem map_integerPolynomial :
    (integerPolynomial p).map (algebraMap ℤ_[p] ℚ_[p]) = polynomial p := by
  simp [integerPolynomial, polynomial]

/-- `X² - p` is irreducible over `ℚ_[p]`. -/
theorem polynomial_irreducible : Irreducible (polynomial p) := by
  rw [← map_integerPolynomial]
  exact ((integerPolynomial_monic p).isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
    (integerPolynomial_irreducible p)

instance polynomialIrreducible : Fact (Irreducible (polynomial p)) :=
  ⟨polynomial_irreducible p⟩

theorem polynomial_monic : (polynomial p).Monic :=
  monic_X_pow_sub_C (p : ℚ_[p]) (by norm_num)

theorem polynomial_natDegree : (polynomial p).natDegree = 2 :=
  natDegree_X_pow_sub_C (p : ℚ_[p])

/-- The field `ℚ_[p]` with a root of `X² - p` adjoined. -/
abbrev Extension := AdjoinRoot (polynomial p)

instance extensionFiniteDimensional : FiniteDimensional ℚ_[p] (Extension p) :=
  (polynomial_monic p).finite_adjoinRoot

/-- The extension `ℚ_[p](√p)/ℚ_[p]` has degree two. -/
theorem finrank_eq_two : Module.finrank ℚ_[p] (Extension p) = 2 := by
  change Module.finrank ℚ_[p] ((ℚ_[p])[X] ⧸ Ideal.span {polynomial p}) = 2
  rw [finrank_quotient_span_eq_natDegree]
  exact polynomial_natDegree p

/-- The canonical generator is a square root of `p`. -/
theorem root_sq :
    AdjoinRoot.root (polynomial p) ^ 2 =
      algebraMap ℚ_[p] (Extension p) (p : ℚ_[p]) := by
  have h := AdjoinRoot.mk_self (f := polynomial p)
  change AdjoinRoot.mk (polynomial p) (X ^ 2 - C (p : ℚ_[p])) = 0 at h
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero,
    AdjoinRoot.algebraMap_eq] using h

end PadicSqrtP
