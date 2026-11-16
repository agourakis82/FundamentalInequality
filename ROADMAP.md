# Roadmap: toward a Mathlib valuation-theory submission

This file plans how the repository grows from the fundamental inequality into
a larger body of valuation theory intended for Mathlib. It is a plan, not a
record of finished work: only Stage 1 is done.

Two rules hold for every stage.

- Everything is built on Mathlib's `ValuativeRel` / `ValuativeExtension` /
  `ValueGroupWithZero` API at the pin (Lean `v4.36.0-rc1`, Mathlib
  `7bb03b4c5313d552989ba5b1c6d3f0f436f65d73`). Nothing imports or restates
  Tau Ceti declarations. Where a Tau Ceti result covers a special case (for
  example `TauCeti.ramificationIndex_mul_inertiaDegree` for nonarchimedean local
  fields), the statement here is proved from Mathlib alone, in greater
  generality, and the overlap is noted rather than imported.
- Each stage builds on the pin, has no `sorry`, adds no axioms beyond
  `propext`, `Classical.choice` and `Quot.sound`, and leaves existing
  statements unchanged.

[`ROADMAP_NODE.md`](ROADMAP_NODE.md) remains the contract for Stage 1 (the
Tau Ceti node draft). Its scope boundary is the boundary of Stage 1; the
stages below are the work beyond it.

Paths below are relative to the Mathlib checkout at the pin. "Not found" means
a search of that checkout found no declaration with the stated content; it is
not a claim that the result is absent from every branch or open PR.

Difficulty: **S** (a few hundred lines), **M** (one substantial file),
**L** (several files, new API), **XL** (a project of its own).

## Overview

| Stage | Content | Status | Difficulty |
| --- | --- | --- | --- |
| 1 | `e`, `f`, towers, fundamental inequality; Artin–Schreier defect example for every prime | done | — |
| 2 | Contrast example `ℚ_p(√p)`: `e = 2`, `f = 1`, `e f = [L:K]` | next | M |
| 3 | Defectless equality `e f = [L:K]` over complete discretely valued fields | next | L |
| 4 | Ostrowski's sum `∑ eᵢ fᵢ ≤ [L:K]` over all extensions; equality conditions | planned | L |
| 5 | Defect: definition, towers, Ostrowski's lemma (`p`-power) | planned | L–XL |
| 6 | Henselian valued fields: uniqueness of extension, henselization | planned | XL |
| 7 | Upstreaming to Mathlib | planned, runs alongside 2–6 | — |

## Stage 1: the fundamental inequality (done)

- **Statement.** For a finite `ValuativeExtension K L` of fields,
  `ramificationIndex K L * residueDegree K L ≤ Module.finrank K L`
  (Kuhlmann, Lemma 6.13), with both invariants positive, multiplicative in
  towers (Lemma 6.16), and `e = f = 1` exactly for immediate extensions.
- **Where.** `FundamentalInequality.lean`; contract in `ROADMAP_NODE.md`.
- **Examples.** `Examples/ArtinSchreierDefect/` proves, for every prime `p`,
  that `X^p - X - t⁻¹` over the perfect hull of `𝔽_p((t))` gives an extension
  with `[L:K] = p`, a unique extension of the valuation, and `e = f = 1`: a
  defect extension with Ostrowski sum `1 < p`.
- **Bridge.** `Examples/Bridge/Completeness.lean` has
  `isRankLeOne_of_finite`, `isNontrivial_of_valuativeExtension`,
  `unique_valuativeRel_of_complete` (over a complete nonarchimedean normed base,
  a compatible rank-at-most-one relation is the one given by the spectral norm),
  and Ostrowski-sum helpers for the unique-extension case (`Extensions`,
  `extensionWeight`, `sum_le_finrank_of_unique`).
- **Mathlib used.** `Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`
  (`ValuativeRel`, `ValuativeExtension`, `ValueGroupWithZero`,
  `mapValueGroupWithZero`, `mapValueGroupWithZero_strictMono`, `IsRankLeOne`,
  `IsNontrivial`, `IsDiscrete`), `Mathlib/RingTheory/Valuation/Extension.lean`
  (`Valuation.HasExtension`), `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`
  (`spectralNorm_unique_field_norm_ext`), `Mathlib/RingTheory/Valuation/RankOne.lean`.

## Stage 2: the contrast example `ℚ_p(√p)` (next)

- **Statement.** For `L = ℚ_p(√p)`, i.e. `ℚ_[p]` adjoined a root of `X² - p`,
  with the valuation extending the `p`-adic one: `[L:K] = 2`, `e = 2`, `f = 1`,
  so `e f = [L:K]` and the extension has no defect.
- **Proof plan.** Irreducibility of `X² - p` from Eisenstein at `p`. The
  extended valuation is unique (Stage 1 bridge, via the spectral norm). Then
  `v(√p)² = v(p)` and `v(p)` generates `v(ℚ_pˣ)`, so `v(√p)` is not in the image
  and `e ≥ 2`. The fundamental inequality gives `e f ≤ 2`, hence `e = 2` and
  `f = 1`. No general equality theorem is imported or used.
- **Mathlib found.** `Mathlib/NumberTheory/Padics/ValuativeRel.lean`
  (`ValuativeRel`-compatible `ℚ_[p]` with `IsNontrivial`, `IsRankLeOne`,
  `IsValuativeTopology`), and `IsNonarchimedeanLocalField ℚ_[p]` in
  `Mathlib/NumberTheory/Padics/LocalField.lean`; `Polynomial.IsEisensteinAt.irreducible` in
  `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean`;
  `Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean`
  (`irreducible_of_eisenstein_criterion`); `IsDiscreteValuationRing ℤ_[p]` in
  `Mathlib/NumberTheory/Padics/PadicIntegers.lean`.
- **Missing.** A ready-made `ValuativeRel` on a finite extension of `ℚ_[p]`;
  it has to be built (spectral norm or `Valuation.RankOne` route, as in the
  Artin–Schreier example).
- **Difficulty.** M. Offered by Demetrios Chiuratto Agourakis.
- **Role.** First instance of Stage 3, and a test case that the Stage 3
  statement must reproduce.

## Stage 3: the defectless equality over complete discretely valued fields (next)

- **Statement.** If `K` is complete for a discrete (rank-one, `IsDiscrete`)
  valuation and `L/K` is finite, then
  `ramificationIndex K L * residueDegree K L = Module.finrank K L`.
  No separability, local compactness, or finite residue field is assumed.
- **Proof plan.** The completeness argument of Serre, *Local Fields*,
  Ch. II §2: with `π` a
  uniformizer of `L` and `u₁, …, u_f` lifting a residue basis, the products
  `uⱼ πⁱ` (`0 ≤ i < e`) are linearly independent (Stage 1, Lemma 6.12) and span
  `𝒪[L]` over `𝒪[K]` by successive approximation, which uses completeness of
  `K`. Steps:
  1. The extension of the valuation to `L` is unique, and `L` is complete
     (Stage 1 bridge; spectral norm).
  2. `IsDiscrete K` and finite index give `IsDiscrete L`.
  3. Spanning by successive approximation, giving the equality.
  4. Bridge lemma: when `𝒪[K]` and `𝒪[L]` are DVRs, `ramificationIndex K L` and
     `residueDegree K L` agree with `Ideal.ramificationIdx` and
     `Ideal.inertiaDeg` of the maximal ideals. This connects the valuative and
     ideal-theoretic APIs.
- **Mathlib found.**
  - `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`:
    `spectralNorm_unique_field_norm_ext`, `spectralNorm_extends`, and the
    `completeSpace` instance for a finite-dimensional extension.
  - `Mathlib/Topology/Algebra/Module/FiniteDimension.lean`:
    `FiniteDimensional.complete`.
  - `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`:
    `Valuation.valuationSubring_isDiscreteValuationRing` (needs a cyclic value
    group); `Mathlib/RingTheory/Valuation/DiscreteValuativeRel.lean`.
  - `Mathlib/NumberTheory/LocalField/Basic.lean`: `IsNonarchimedeanLocalField`,
    with instances `IsDiscreteValuationRing 𝒪[K]`, `ValuativeRel.IsDiscrete K`,
    `CompleteSpace K`, `IsAdicComplete 𝓂[K] 𝒪[K]`, and
    `valueGroupWithZeroIsoInt`. Stage 3 specializes to local fields through
    these instances.
  - `Mathlib/RingTheory/RamificationInertia/Ramification.lean`
    (`Ideal.ramificationIdx`), `.../Inertia.lean` (`Ideal.inertiaDeg`),
    `.../Basic.lean` (`Ideal.sum_ramification_inertia_eq_finrank`: for
    `S` finite flat over a domain `R`, `∑ e f = finrank R S`).
  - `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`:
    `IsIntegralClosure.finite` and `IsIntegralClosure.isDedekindDomain`.
- **Missing.** Finiteness of `𝒪[L]` over `𝒪[K]` for an inseparable `L/K`:
  `IsIntegralClosure.finite` assumes `Algebra.IsSeparable K L`. The direct
  approximation argument avoids this. The alternative route through
  `Ideal.sum_ramification_inertia_eq_finrank` needs `Module.Finite 𝒪[K] 𝒪[L]`,
  so it covers only the separable case unless that finiteness is proved
  separately.
- **Difficulty.** L.
- **Overlap.** For local fields this is the statement of
  `TauCeti.ramificationIndex_mul_inertiaDegree`. The result here is proved from
  Mathlib alone and is more general; the comparison is a note, not a lemma.

## Stage 4: Ostrowski's sum over all extensions (planned)

- **Statement.** For a finite `L/K` and a valuation on `K`, the extensions
  `w₁, …, w_g` of the valuation to `L` are finite in number and
  `∑ e(wᵢ) f(wᵢ) ≤ [L:K]`. Equality holds when, for example, the valuation
  ring of `K` is a DVR and its integral closure in `L` is finite over it.
- **Proof plan.** Existence of extensions (Chevalley); finiteness of their
  number (at most the separable degree); independence of the products from
  Lemma 6.12 across several extensions, using an approximation theorem for
  pairwise incomparable valuation rings. The current `Extensions` type and
  `sum_le_finrank_of_unique` in `Examples/Bridge/Completeness.lean` handle the
  case of one extension and become a corollary.
- **Mathlib found.**
  - `Mathlib/RingTheory/Valuation/LocalSubring.lean`:
    `LocalSubring.exists_valuationRing_of_isMax`,
    `LocalSubring.mem_of_isMax_of_isIntegral` (the Chevalley-type existence
    argument).
  - `Mathlib/RingTheory/Valuation/Integral.lean`: `Valuation.Integers`
    integrality lemmas.
  - `Mathlib/Analysis/AbsoluteValue/Equivalence.lean`:
    `AbsoluteValue.denseRange_algebraMap_pi` (weak approximation for finitely
    many pairwise inequivalent real absolute values). This covers rank one
    only.
  - `Mathlib/RingTheory/RamificationInertia/Basic.lean`:
    `Ideal.sum_ramification_inertia_eq_finrank`, the Dedekind/flat analogue,
    usable for the equality case once Stage 3's bridge lemma exists.
- **Missing.** An approximation theorem for finitely many incomparable
  valuations of arbitrary rank (not found); a type of all extensions of a
  `ValuativeRel` along `K → L` with a `Finite` instance (not found).
- **Difficulty.** L.

## Stage 5: the defect (planned)

- **Statement.** When the valuation has a unique extension to `L` (for example
  `K` henselian), define the defect `d(L/K) = [L:K] / (e f)`. Then `d` is a
  positive integer, `d` is multiplicative in towers, and (Ostrowski's lemma)
  `d` is a power of the characteristic exponent of the residue field: `d = 1`
  in residue characteristic `0`, `d = pᵏ` in residue characteristic `p`.
- **Proof plan.** Integrality and towers follow from Stage 1
  (`residueDegree_mul`, `ramificationIndex_mul`) and the degree tower law.
  Ostrowski's lemma needs ramification theory: reduce to a Galois extension,
  use the decomposition and inertia groups, and show the tamely ramified part
  is defectless, so the defect is concentrated in the wild ramification group,
  a `p`-group.
- **Mathlib found.** `Module.finrank_mul_finrank`;
  `Mathlib/RingTheory/Valuation/RamificationGroup.lean`
  (`ValuationSubring.decompositionSubgroup`, `ValuationSubring.inertiaSubgroup`).
- **Missing.** Any notion of defect, defectless field, or tame extension
  (no matches for `defect`/`defectless`/`henselization` in the Mathlib tree);
  higher ramification groups of a valuation; the relation between the order
  of the inertia group and `e f`.
- **Examples.** The Artin–Schreier example already has `d = p`; Stage 2 has
  `d = 1`.
- **Difficulty.** L for the definition and towers; XL for Ostrowski's lemma.

## Stage 6: henselian valued fields (planned)

- **Statement.** For a valued field `(K, v)`, the following are equivalent:
  `𝒪[K]` is a henselian local ring; `v` extends uniquely to every algebraic
  extension. Every valued field has a henselization, an immediate extension
  with a universal property. Complete rank-one fields are henselian.
- **Mathlib found.**
  - `Mathlib/RingTheory/Henselian.lean`: `HenselianRing`, `HenselianLocalRing`,
    `HenselianLocalRing.TFAE`, `IsAdicComplete.henselianRing`.
  - `Mathlib/NumberTheory/Padics/Hensel.lean`: `hensels_lemma` for `ℤ_[p]`.
  - `Mathlib/Analysis/Normed/Field/Krasner.lean`: `IsKrasner`,
    `IsKrasner.of_completeSpace_of_normal`.
  - `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`: uniqueness of the
    extended norm over a complete base (already used in Stage 1's bridge).
- **Missing.** A henselian valued-field class stated with `ValuativeRel`; the
  equivalence with unique extension for valuations of arbitrary rank; the
  henselization and its immediacy (none found).
- **Difficulty.** XL. The rank-one complete case is close to what Stage 1's
  bridge already proves and can come first.

## Stage 7: upstreaming plan (planned, alongside Stages 2–6)

Order, each step a separate Mathlib PR that depends only on earlier ones:

1. **Small general lemmas from the bridge.** `isRankLeOne_of_finite` and
   `isNontrivial_of_valuativeExtension`, next to `ValuativeExtension` in
   `Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`.
2. **The invariants.** `residueDegree`, `ramificationIndex`, `IsImmediate`,
   towers, and the `ValuativeExtension` identity instance, as a new file under
   `Mathlib/RingTheory/Valuation/ValuativeRel/` (Layer 0 of `ROADMAP_NODE.md`).
3. **The fundamental inequality.** Lemma 6.12 and 6.13 (Layers 1–2), in the
   same directory.
4. **Uniqueness over complete rank-one fields.** `unique_valuativeRel_of_complete`,
   near `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` or
   `Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`.
5. **Stage 3 and its bridge lemma** to `Ideal.ramificationIdx` /
   `Ideal.inertiaDeg`.
6. **Stage 4, then Stage 5, then Stage 6.**

Worked examples (Artin–Schreier, `ℚ_p(√p)`) stay in this repository or go to
`MathlibTest/` / `Archive/`, depending on reviewer preference; they are not
library material as written.

Style and naming work before step 2:

- **Naming.** Mathlib's ideal-theoretic names are `Ideal.ramificationIdx` and
  `Ideal.inertiaDeg`. Decide with reviewers whether the valuative names stay
  `ValuativeExtension.ramificationIndex` / `residueDegree` or align with the
  ideal names. The bridge lemma of Stage 3 should name both.
- **Duplication.** About 650 lines of the `p = 2` chain in
  `Examples/ArtinSchreierDefect/Residue.lean` duplicate
  `Examples/ArtinSchreierDefect/ResidueGeneral.lean` and can be removed before
  any upstreaming of example material.
- **Conventions.** Module docstrings with references, `@[simp]` only on
  normal-form lemmas, no `Examples.*` namespace in library files, and the
  `weak.linter.mathlibStandardSet` linters (already enabled in `lakefile.toml`)
  clean.
- **Deprecations at the pin.** `Mathlib/NumberTheory/RamificationInertia/Valuation.lean`
  is a deprecated module (since 2026-10-09); its content is in
  `Mathlib/RingTheory/DedekindDomain/AdicValuation/Ramification.lean`. The
  `Ideal.sum_ramification_inertia` of
  `Mathlib/NumberTheory/RamificationInertia/Basic.lean` is deprecated in favour
  of `Mathlib/RingTheory/RamificationInertia/Basic.lean`. New code should cite
  the current files.

## References

- Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation, Chapter 6
  (`kuhlmannValuation`).
- N. Bourbaki, *Commutative Algebra*, Chapter VI (`bourbaki1989b`).
- J.-P. Serre, *Local Fields*, Chapter II, §2 (`serreLocalFields`).
- A. J. Engler and A. Prestel, *Valued Fields*, Chapters 3–5, for the
  approximation theorem, henselian fields, and the defect
  (`englerPrestel2005`).
