/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Residue

/-!
# The Artin–Schreier defect example

This is the root module for the example. The development is split as follows:

* `Examples.ArtinSchreierDefect.Basic`: Laurent base, perfect hull, and the
  irreducible degree-`p` Artin–Schreier extension for every prime `p`.
* `Examples.Bridge.Completeness`: rank lifting, uniqueness from
  completeness of the base, and the abstract Ostrowski-sum comparison.
* `Examples.ArtinSchreierDefect.Valuation`: spectral valuations, ramification
  index one, and uniqueness of a compatible valuative relation, using
  `ValuativeExtension.tower` for compatibility along the tower.
* `Examples.ArtinSchreierDefect.ResidueGeneral`: residue degree one and the
  unconditional Ostrowski sum `Σ eᵢfᵢ = ef = 1 < p = [L:K]`.
* `Examples.ArtinSchreierDefect.Residue`: the backwards-compatible quadratic
  API at `p = 2` and the numerical defect quotient.

The construction is uniform in `p`; the original quadratic declarations are
one-line specialisations where their statements coincide with the general API.
-/

@[expose] public section
