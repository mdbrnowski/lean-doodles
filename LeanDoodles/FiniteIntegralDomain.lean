/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Finite.Card
import Mathlib.RingTheory.LittleWedderburn

open Function

/-- Every finite integral domain is a field. -/
theorem finite_integral_domain_is_field (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R := by
  constructor
  · -- Fields have two distinct elements.
    exact IsDomain.mk.exists_pair_ne
  · -- Fields are commutative.
    exact CommRing.mul_comm
  · -- Nonzero elements have multiplicative inverses.
    intro a ha
    let f : R → R := fun x => a * x
    have h_inj : Injective f :=
      fun x y h => mul_left_cancel₀ ha (h : f x = f y)
    have h_surj : Surjective f :=
      Finite.injective_iff_surjective.mp h_inj
    exact h_surj 1

/-- Every finite integral domain is a field. The proof is derived from a more general theorem,
the proof of which relies on more advanced mathematics (like Wedderburn's little theorem). -/
theorem finite_integral_domain_is_field' (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R :=
  Finite.isDomain_to_isField R
